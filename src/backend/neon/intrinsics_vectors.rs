//! Differential test vectors for the Lean model of [`super::intrinsics`].
//!
//! `lean/Kopis/Neon/Intrinsics.lean` asserts, as 46 axioms, what each wrapper in
//! [`super::intrinsics`] does to a 128-bit word. Those axioms are the entire trust base the NEON
//! backend adds, they were written by reading the Arm ARM, and *nothing in the proof checks
//! them*: an axiom that is wrong makes every NEON theorem worthless, silently.
//!
//! This module closes half of that gap. It runs every wrapper on this CPU over a fixed, seeded
//! set of inputs and records the results in `tests/neon_intrinsics_vectors.jsonl`;
//! `lean/SpecTests/Neon/Run.lean` replays the same inputs through the *computable* models in
//! `lean/Kopis/Neon/Model.lean`, which `Model.lean` proves are exactly what the axioms assert.
//! Model disagrees with silicon ⇒ an axiom is wrong ⇒ the runner fails.
//!
//! What this does not do: it is a test, not a proof. Agreement on ~1000 inputs per operation is
//! evidence that the axiom is right everywhere, not a demonstration of it.
//!
//! # One interface, one recorded file
//!
//! Four of the wrappers are FEAT_SHA3 instructions and six more exist only to serve them, so the
//! recorded file only makes sense for a `+sha3` build. That is the only build there is: the
//! backend as a whole is compiled only where `build.rs` confirmed the extension, so the interface
//! this replays never varies and the vectors stay one file rather than two. It matches the
//! extraction's own scope too — `../extract_rust_to_lean.sh` extracts the NEON backend with
//! `-C target-feature=+sha3`, so the `+sha3` build is the one the proofs are about.
//! `aarch64-apple-darwin` enables `sha3` by default, so a plain `cargo test` on Apple silicon
//! runs this.
//!
//! # Reading a vector back out
//!
//! Every input is built with `load_*` and every output read with `store_i16`, so a *symmetric*
//! byte-order error in that pair would cancel and go unnoticed. [`readback_byte_order`] pins the
//! read-back path down independently: `dup_n_s16(0x1234)` names the bytes of each lane without
//! any load being involved, so a byte-swapped store cannot survive it.
//!
//! # Structured inputs are not optional
//!
//! Three of the operations here are *vacuous* on uniformly random input, and each needed its own
//! generator:
//!
//! * `tbl1_u8` zeroes any lane whose index byte is ≥ 16, which a uniform byte is with
//!   probability 15/16 — random controls would test "returns zero" and nothing else.
//! * `ushl_u16` / `ushl_u32` take a *signed* per-lane count and shift the lane out entirely
//!   beyond ±16 / ±32, so uniform counts are almost always a wordy way of writing zero.
//! * `sqdmulh_s16` saturates only when both operands are −2^15, which uniform input never hits.
//!
//! The AVX2 sibling learned the same lesson from a deliberately-corrupted-model check that
//! *passed*; see the Phase A note in `lean/AVX2_VERIFICATION_PLAN.md`. If anyone adds an
//! operation here, ask what its interesting inputs are before trusting a pass.
//!
//! # Running
//!
//! `cargo test` on an AArch64 machine with the SHA3 extension *checks* the committed file
//! against this CPU — so drift between the recorded vectors and real hardware is caught
//! continuously, not just when someone remembers to regenerate. To (re)create the file:
//!
//! ```sh
//! RUSTFLAGS='-C target-feature=+sha3' KOPIS_REGEN_VECTORS=1 \
//!   cargo test --lib neon::intrinsics_vectors
//! ```

use super::intrinsics::*;
use std::string::String;
use std::vec::Vec;

/// Random inputs per operation. The Lean-side acceptance bar is ≥ 1000.
const N_RANDOM: usize = 1000;

/// Random inputs per memory accessor. Fewer would do: their input space is an offset and a
/// buffer, with no arithmetic to get wrong beyond the little-endian reading.
const N_MEMORY: usize = 1000;

/// Fixed seed, so the file is reproducible on any AArch64 host.
const SEED: u64 = 0x4B6F_7069_734E_454F;

// ---------------------------------------------------------------------------------------
// Deterministic RNG (splitmix64) — a dev-dependency's generator would tie the recorded
// vectors to that crate's version.
// ---------------------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn fill(&mut self, out: &mut [u8]) {
        for chunk in out.chunks_mut(8) {
            let word = self.u64().to_le_bytes();
            chunk.copy_from_slice(&word[..chunk.len()]);
        }
    }

    fn bytes16(&mut self) -> [u8; 16] {
        let mut out = [0u8; 16];
        self.fill(&mut out);
        out
    }

    fn below(&mut self, n: u64) -> u64 {
        self.u64() % n
    }

    /// A vector whose 32-bit lanes sit *near a boundary* rather than uniformly at random.
    ///
    /// Uniform lanes essentially never land within a few counts of ±32767 or ±65535, so they do
    /// not exercise the narrowing and comparison wrappers' edges at all. In the 16-bit lane view
    /// these also produce the `0x0000` / `0x7FFF` / `0x8000` / `0xFFFF` halves that
    /// `sqdmulh_s16`'s saturation and `cmgt_s32`'s sign handling turn on.
    fn structured(&mut self) -> [u8; 16] {
        const BASES: [i64; 12] = [
            0,
            1,
            32767,
            32768,
            65535,
            65536,
            -1,
            -32768,
            -32769,
            -65535,
            i32::MIN as i64,
            i32::MAX as i64,
        ];
        let mut out = [0u8; 16];
        for lane in 0..4 {
            let base = BASES[self.below(BASES.len() as u64) as usize];
            let delta = self.below(5) as i64 - 2;
            let v = base.wrapping_add(delta) as i32;
            out[4 * lane..4 * lane + 4].copy_from_slice(&v.to_le_bytes());
        }
        out
    }

    /// A random vector: usually uniform, sometimes boundary-hugging.
    fn mixed(&mut self) -> [u8; 16] {
        if self.below(3) == 0 {
            self.structured()
        } else {
            self.bytes16()
        }
    }

    /// A `tbl` control vector: bytes drawn from `0..20`, so most lanes select a real byte and
    /// about a fifth take the out-of-range path that yields zero. A uniform byte is ≥ 16 with
    /// probability 15/16, which would make the operation look like a constant zero.
    fn table_idx(&mut self) -> [u8; 16] {
        let mut out = [0u8; 16];
        for b in out.iter_mut() {
            *b = self.below(20) as u8;
        }
        out
    }

    /// A `ushl` count vector with `LANES` lanes of `width` bits: per-lane signed counts drawn
    /// from `-(width + 2) ..= width + 2`, so both directions and the shift-everything-out edge
    /// are covered. Uniform counts would be out of range in essentially every lane.
    fn shift_counts(&mut self, lanes: usize, width: i64) -> [u8; 16] {
        let bytes = 16 / lanes;
        let span = 2 * (width + 2) + 1;
        let mut out = [0u8; 16];
        for lane in 0..lanes {
            let c = self.below(span as u64) as i64 - (width + 2);
            let le = c.to_le_bytes();
            out[lane * bytes..(lane + 1) * bytes].copy_from_slice(&le[..bytes]);
        }
        out
    }
}

// ---------------------------------------------------------------------------------------
// Getting bytes into and out of a vector
// ---------------------------------------------------------------------------------------

/// A `Vec128` holding the given 16 bytes, least significant first.
#[target_feature(enable = "neon")]
fn v_of(bytes: &[u8; 16]) -> Vec128 {
    load_u8x16(bytes, 0)
}

/// The 16 bytes of a `Vec128`, least significant first.
#[target_feature(enable = "neon")]
fn v_bytes(v: Vec128) -> [u8; 16] {
    let mut elems = [0i16; 8];
    store_i16(&mut elems, 0, v);
    let mut out = [0u8; 16];
    for (k, e) in elems.iter().enumerate() {
        out[2 * k..2 * k + 2].copy_from_slice(&e.to_le_bytes());
    }
    out
}

// ---------------------------------------------------------------------------------------
// Record emission
// ---------------------------------------------------------------------------------------

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(2 * bytes.len());
    for b in bytes {
        for nibble in [b >> 4, b & 0xF] {
            s.push(char::from_digit(nibble as u32, 16).unwrap_or('?'));
        }
    }
    s
}

/// One `.jsonl` line. Fields are written in a fixed order so the file is byte-reproducible;
/// every value is a hex string in memory order (least significant byte first) or a number.
struct Rec {
    out: String,
}

impl Rec {
    fn new(op: &str) -> Self {
        let mut out = String::with_capacity(256);
        out.push_str("{\"op\":\"");
        out.push_str(op);
        out.push('"');
        Rec { out }
    }

    fn hex(mut self, key: &str, bytes: &[u8]) -> Self {
        self.out.push_str(",\"");
        self.out.push_str(key);
        self.out.push_str("\":\"");
        self.out.push_str(&hex(bytes));
        self.out.push('"');
        self
    }

    fn num(mut self, key: &str, n: i64) -> Self {
        self.out.push_str(",\"");
        self.out.push_str(key);
        self.out.push_str("\":");
        self.out.push_str(&std::format!("{n}"));
        self
    }

    fn emit(self, sink: &mut String) {
        sink.push_str(&self.out);
        sink.push_str("}\n");
    }
}

/// Instantiates a const-generic wrapper at a runtime immediate.
macro_rules! imm_call {
    ($imm:expr, $f:ident, $args:tt, [$($n:literal),*]) => {
        match $imm { $( $n => $f::<$n> $args, )* _ => std::unreachable!() }
    };
}

/// Patterns worth trying before the random ones: saturation boundaries, sign-bit boundaries,
/// the byte values `tbl` reads as "zero this lane", and plain counting.
fn edge_cases() -> Vec<[u8; 16]> {
    let rep = |pat: [u8; 4]| -> [u8; 16] {
        let mut out = [0u8; 16];
        for (i, b) in out.iter_mut().enumerate() {
            *b = pat[i % 4];
        }
        out
    };
    let mut counting = [0u8; 16];
    for (i, b) in counting.iter_mut().enumerate() {
        *b = i as u8;
    }
    let mut descending = [0u8; 16];
    for (i, b) in descending.iter_mut().enumerate() {
        *b = 15 - i as u8;
    }
    std::vec![
        [0u8; 16],
        [0xFF; 16],
        rep([0x00, 0x80, 0x00, 0x80]), // i16::MIN in every 16-bit lane: sqdmulh's one saturation
        rep([0xFF, 0x7F, 0xFF, 0x7F]), // i16::MAX in every 16-bit lane
        rep([0x00, 0x00, 0x00, 0x80]), // i32::MIN in every 32-bit lane
        rep([0xFF, 0xFF, 0xFF, 0x7F]), // i32::MAX in every 32-bit lane
        rep([0x01, 0x00, 0xFF, 0xFF]), // +1 / -1 alternating 16-bit lanes
        counting,                      // the identity `tbl` control
        descending,                    // the reversing `tbl` control
    ]
}

// ---------------------------------------------------------------------------------------
// The vectors
// ---------------------------------------------------------------------------------------

/// Runs every wrapper over the fixed input set and returns the `.jsonl` contents.
#[target_feature(enable = "neon,sha3")]
fn build() -> String {
    let mut rng = Rng(SEED);
    let mut o = String::with_capacity(8 << 20);
    let edges = edge_cases();

    // --- one-argument lane operations --------------------------------------------------
    macro_rules! unop {
        ($name:ident) => {{
            let mut run = |a: [u8; 16]| {
                let r = v_bytes($name(v_of(&a)));
                Rec::new(stringify!($name))
                    .hex("a", &a)
                    .hex("o", &r)
                    .emit(&mut o);
            };
            for a in &edges {
                run(*a);
            }
            for _ in 0..N_RANDOM {
                run(rng.mixed());
            }
        }};
    }

    unop!(cnt_u8);
    unop!(sxtl_low_s16);
    unop!(sxtl_high_s16);

    // --- two-argument lane operations --------------------------------------------------
    //
    // Each is exercised on every ordered pair of edge patterns and then on `N_RANDOM` random
    // pairs. `$name` is both the wrapper and the string the Lean runner dispatches on.
    macro_rules! binop {
        ($name:ident) => {
            binop!($name, mixed)
        };
        ($name:ident, $gen_b:ident) => {{
            let mut run = |a: [u8; 16], b: [u8; 16]| {
                let r = v_bytes($name(v_of(&a), v_of(&b)));
                Rec::new(stringify!($name))
                    .hex("a", &a)
                    .hex("b", &b)
                    .hex("o", &r)
                    .emit(&mut o);
            };
            for a in &edges {
                for b in &edges {
                    run(*a, *b);
                }
            }
            for _ in 0..N_RANDOM {
                let a = rng.mixed();
                let b = rng.$gen_b();
                run(a, b);
            }
        }};
    }

    binop!(and);
    binop!(eor);
    binop!(add_16);
    binop!(sub_16);
    binop!(mul_16);
    binop!(sqdmulh_s16);
    binop!(shsub_s16);
    binop!(add_32);
    binop!(sub_32);
    binop!(cmgt_s32);
    binop!(smull_low_s16);
    binop!(smull_high_s16);
    binop!(xtn_pair_32);
    binop!(shrn16_pair_s32);
    binop!(trn1_16);
    binop!(trn2_16);
    binop!(trn1_32);
    binop!(trn2_32);
    binop!(trn1_64);
    binop!(trn2_64);
    binop!(rax1);

    // The three whose second operand has to be drawn on purpose — see the module docs.
    binop!(tbl1_u8, table_idx);

    macro_rules! shift_by_vector {
        ($name:ident, $lanes:expr, $width:expr) => {{
            let mut run = |a: [u8; 16], b: [u8; 16]| {
                let r = v_bytes($name(v_of(&a), v_of(&b)));
                Rec::new(stringify!($name))
                    .hex("a", &a)
                    .hex("b", &b)
                    .hex("o", &r)
                    .emit(&mut o);
            };
            for a in &edges {
                for b in &edges {
                    run(*a, *b);
                }
            }
            for _ in 0..N_RANDOM {
                let a = rng.mixed();
                let b = rng.shift_counts($lanes, $width);
                run(a, b);
            }
        }};
    }

    shift_by_vector!(ushl_u16, 8, 16);
    shift_by_vector!(ushl_u32, 4, 32);

    // --- three-argument lane operations ------------------------------------------------
    macro_rules! terop {
        ($name:ident) => {{
            let mut run = |a: [u8; 16], b: [u8; 16], c: [u8; 16]| {
                let r = v_bytes($name(v_of(&a), v_of(&b), v_of(&c)));
                Rec::new(stringify!($name))
                    .hex("a", &a)
                    .hex("b", &b)
                    .hex("c", &c)
                    .hex("o", &r)
                    .emit(&mut o);
            };
            for a in &edges {
                for b in &edges {
                    for c in &edges {
                        run(*a, *b, *c);
                    }
                }
            }
            for _ in 0..N_RANDOM {
                let a = rng.mixed();
                let b = rng.mixed();
                let c = rng.mixed();
                run(a, b, c);
            }
        }};
    }

    terop!(mla_32);
    terop!(eor3);
    terop!(bcax);

    // --- shift by an immediate ----------------------------------------------------------
    //
    // `sshr` takes 1..=16 at 16-bit lanes. The immediate is drawn uniformly from that whole
    // range rather than pinned to the three the backend uses, since the axiom quantifies over it.
    let sshr_inputs: Vec<[u8; 16]> = edges
        .iter()
        .copied()
        .chain((0..N_RANDOM).map(|_| rng.mixed()))
        .collect();
    for a in sshr_inputs {
        let imm = 1 + rng.below(16) as i32;
        let r = v_bytes(imm_call!(
            imm,
            sshr_n_s16,
            (v_of(&a)),
            [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
        ));
        Rec::new("sshr_n_s16")
            .hex("a", &a)
            .num("imm", imm as i64)
            .hex("o", &r)
            .emit(&mut o);
    }

    // `xar` takes 0..=63; Keccak's rho uses 25 distinct ones, and the axiom covers all of them.
    let xar_inputs: Vec<[u8; 16]> = edges
        .iter()
        .copied()
        .chain((0..N_RANDOM).map(|_| rng.mixed()))
        .collect();
    for a in xar_inputs {
        let b = rng.mixed();
        let imm = rng.below(64) as i32;
        let r = v_bytes(imm_call!(
            imm,
            xar,
            (v_of(&a), v_of(&b)),
            [
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
                44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63
            ]
        ));
        Rec::new("xar")
            .hex("a", &a)
            .hex("b", &b)
            .num("imm", imm as i64)
            .hex("o", &r)
            .emit(&mut o);
    }

    // --- broadcasts, whose input is a scalar --------------------------------------------
    macro_rules! dup {
        ($name:ident, $ty:ty) => {{
            for _ in 0..N_RANDOM {
                let x = rng.u64() as $ty;
                let r = v_bytes($name(x));
                Rec::new(stringify!($name))
                    .hex("a", &x.to_le_bytes())
                    .hex("o", &r)
                    .emit(&mut o);
            }
        }};
    }

    dup!(dup_n_s16, i16);
    dup!(dup_n_u16, u16);
    dup!(dup_n_s32, i32);
    dup!(dup_n_u32, u32);
    dup!(dup_n_u64, u64);

    for _ in 0..N_RANDOM {
        let lo = rng.u64();
        let hi = rng.u64();
        let r = v_bytes(set_u64x2(lo, hi));
        Rec::new("set_u64x2")
            .hex("a", &lo.to_le_bytes())
            .hex("b", &hi.to_le_bytes())
            .hex("o", &r)
            .emit(&mut o);
    }

    // --- memory: the vector-indexed accessors -------------------------------------------
    macro_rules! load_test {
        ($name:ident, $elem:ty, $n_elem:expr, $vec_elems:expr) => {{
            const NB: usize = $n_elem * core::mem::size_of::<$elem>();
            let vectors = $n_elem / $vec_elems;
            for _ in 0..N_MEMORY {
                let mut raw = [0u8; NB];
                rng.fill(&mut raw);
                let mut buf = [0 as $elem; $n_elem];
                for (k, e) in buf.iter_mut().enumerate() {
                    let sz = core::mem::size_of::<$elem>();
                    let mut le = [0u8; core::mem::size_of::<$elem>()];
                    le.copy_from_slice(&raw[k * sz..(k + 1) * sz]);
                    *e = <$elem>::from_le_bytes(le);
                }
                let idx = rng.below(vectors as u64) as usize;
                let r = v_bytes($name(&buf, idx));
                Rec::new(stringify!($name))
                    .hex("buf", &raw)
                    .num("idx", idx as i64)
                    .hex("o", &r)
                    .emit(&mut o);
            }
        }};
    }

    load_test!(load_i16, i16, 32, 8);
    load_test!(load_u16, u16, 32, 8);
    load_test!(load_i32, i32, 16, 4);

    macro_rules! store_test {
        ($name:ident, $elem:ty, $n_elem:expr, $vec_elems:expr) => {{
            const NB: usize = $n_elem * core::mem::size_of::<$elem>();
            let vectors = $n_elem / $vec_elems;
            for _ in 0..N_MEMORY {
                let mut raw = [0u8; NB];
                rng.fill(&mut raw);
                let mut buf = [0 as $elem; $n_elem];
                for (k, e) in buf.iter_mut().enumerate() {
                    let sz = core::mem::size_of::<$elem>();
                    let mut le = [0u8; core::mem::size_of::<$elem>()];
                    le.copy_from_slice(&raw[k * sz..(k + 1) * sz]);
                    *e = <$elem>::from_le_bytes(le);
                }
                let idx = rng.below(vectors as u64) as usize;
                let val = rng.bytes16();
                $name(&mut buf, idx, v_of(&val));
                let mut after = [0u8; NB];
                for (k, e) in buf.iter().enumerate() {
                    let sz = core::mem::size_of::<$elem>();
                    after[k * sz..(k + 1) * sz].copy_from_slice(&e.to_le_bytes());
                }
                Rec::new(stringify!($name))
                    .hex("buf", &raw)
                    .num("idx", idx as i64)
                    .hex("v", &val)
                    .hex("o", &after)
                    .emit(&mut o);
            }
        }};
    }

    store_test!(store_i16, i16, 32, 8);
    store_test!(store_u16, u16, 32, 8);
    store_test!(store_i32, i32, 16, 4);

    // --- memory: the byte-indexed accessors ---------------------------------------------
    //
    // `keccak` reads and writes the sponge a 64-bit word at a time and `ser` reads groups at
    // multiples of the coefficient width, so these offsets are multiples of neither 16 nor each
    // other. The offsets drawn below are unrestricted, which covers both and more.
    for _ in 0..N_MEMORY {
        let mut raw = [0u8; 48];
        rng.fill(&mut raw);
        let off = rng.below(33) as usize;
        let r = v_bytes(load_u8x16(&raw, off));
        Rec::new("load_u8x16")
            .hex("buf", &raw)
            .num("idx", off as i64)
            .hex("o", &r)
            .emit(&mut o);
    }

    for _ in 0..N_MEMORY {
        let mut raw = [0u8; 48];
        rng.fill(&mut raw);
        let off = rng.below(33) as usize;
        let val = rng.bytes16();
        let mut after = raw;
        store_u8x16(&mut after, off, v_of(&val));
        Rec::new("store_u8x16")
            .hex("buf", &raw)
            .num("idx", off as i64)
            .hex("v", &val)
            .hex("o", &after)
            .emit(&mut o);
    }

    o
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

/// The path the Lean runner reads.
fn vectors_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/neon_intrinsics_vectors.jsonl")
}

/// Anchors the read-back path: `dup_n_*` fixes the bytes of every lane without any load being
/// involved, so this fails if `store_i16` has the byte order wrong — which a `load`-then-`store`
/// round trip could not detect on its own.
#[test]
fn readback_byte_order() {
    if !super::available() {
        return;
    }
    // SAFETY: guarded by the `available()` check above.
    unsafe {
        assert_eq!(v_bytes(dup_n_s16(0x1234)), [0x34, 0x12].repeat(8)[..]);
        assert_eq!(
            v_bytes(dup_n_s32(0x1234_5678)),
            [0x78, 0x56, 0x34, 0x12].repeat(4)[..]
        );
        assert_eq!(
            v_bytes(dup_n_u64(0x0102_0304_0506_0708)),
            [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01].repeat(2)[..]
        );
        assert_eq!(v_bytes(set_u64x2(0, u64::MAX)), {
            let mut want = [0u8; 16];
            want[8..].copy_from_slice(&[0xFF; 8]);
            want
        });
    }
}

/// Checks the committed vectors against this CPU, or regenerates them when
/// `KOPIS_REGEN_VECTORS` is set.
#[test]
fn vectors_match_this_cpu() {
    if !super::available() {
        return;
    }
    // SAFETY: guarded by the `available()` check above; the backend is compiled only when
    // `build.rs` confirmed the SHA3 extension for the target.
    let produced = unsafe { build() };
    let path = vectors_path();

    if std::env::var_os("KOPIS_REGEN_VECTORS").is_some() {
        std::fs::write(&path, &produced).expect("writing neon_intrinsics_vectors.jsonl");
        return;
    }

    let committed = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        std::panic!(
            "{}: {e}\nrun `KOPIS_REGEN_VECTORS=1 cargo test --lib neon::intrinsics_vectors` \
             on an AArch64 host with the SHA3 extension to create it",
            path.display()
        )
    });
    assert!(
        committed == produced,
        "tests/neon_intrinsics_vectors.jsonl disagrees with this CPU ({} vs {} bytes). \
         Either the wrappers changed or the recorded vectors are stale.",
        committed.len(),
        produced.len()
    );
}
