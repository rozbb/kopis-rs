//! Differential test vectors for the Lean model of [`super::intrinsics`].
//!
//! `lean/Kopis/Avx2/Intrinsics.lean` asserts, as 45 axioms, what each wrapper in
//! [`super::intrinsics`] does to a 256-bit word.  Those axioms are the entire trust base the
//! AVX2 backend adds, they were written by reading the Intel SDM, and *nothing in the proof
//! checks them*: an axiom that is wrong makes every AVX2 theorem worthless, silently.
//!
//! This module closes half of that gap.  It runs every wrapper on this CPU over a fixed,
//! seeded set of inputs and records the results in `tests/intrinsics_vectors.jsonl`;
//! `lean/SpecTests/Avx2/Run.lean` replays the same inputs through the *computable* models in
//! `lean/Kopis/Avx2/Model.lean`, which `Model.lean` proves are exactly what the axioms assert.
//! Model disagrees with silicon ⇒ an axiom is wrong ⇒ the runner fails.
//!
//! What this does not do: it is a test, not a proof.  Agreement on ~1000 inputs per operation
//! is evidence that the axiom is right everywhere, not a demonstration of it.
//!
//! # Reading a vector back out
//!
//! Every input is built with `load_*` and every output read with `store_i16`, so a *symmetric*
//! byte-order error in that pair would cancel and go unnoticed.  [`readback_byte_order`] pins
//! the read-back path down independently: `set1_epi16(0x1234)` names the bytes of each lane
//! without any load being involved, so a byte-swapped store cannot survive it.
//!
//! # Running
//!
//! `cargo test` on an AVX2 machine *checks* the committed file against this CPU — so drift
//! between the recorded vectors and real hardware is caught continuously, not just when someone
//! remembers to regenerate.  To (re)create the file:
//!
//! ```sh
//! KOPIS_REGEN_VECTORS=1 cargo test --lib intrinsics_vectors
//! ```

use super::intrinsics::*;
use std::string::String;
use std::vec::Vec;

/// Random inputs per operation.  The Lean-side acceptance bar is ≥ 1000.
const N_RANDOM: usize = 1000;

/// Random inputs per memory accessor.  Fewer: their input space is an offset and a buffer, with
/// no arithmetic to get wrong beyond the little-endian reinterpretation the `*_of_*` ones claim.
const N_MEMORY: usize = 1000;

/// Fixed seed, so the file is reproducible on any AVX2 host.
const SEED: u64 = 0x4B6F_7069_7341_5658;

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

    fn bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        self.fill(&mut out);
        out
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
    /// Uniform 32-bit lanes essentially never land within a few counts of ±32767 or ±65535, so
    /// they do not exercise `vpackssdw` / `vpackusdw` saturation at all: every random lane
    /// saturates, and a model that clamped at the wrong threshold would still agree with
    /// hardware on every one of them.  (That is not hypothetical — it is what the first
    /// deliberately-corrupted-model check found.)  In the 16-bit lane view these also produce
    /// the `0x0000` / `0x7FFF` / `0x8000` / `0xFFFF` halves that `vpmulhw` and `vpcmpgtd` turn
    /// on.
    fn structured32(&mut self) -> [u8; 32] {
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
        let mut out = [0u8; 32];
        for lane in 0..8 {
            let base = BASES[self.below(BASES.len() as u64) as usize];
            let delta = self.below(5) as i64 - 2;
            let v = base.wrapping_add(delta) as i32;
            out[4 * lane..4 * lane + 4].copy_from_slice(&v.to_le_bytes());
        }
        out
    }

    /// A random vector: usually uniform, sometimes boundary-hugging.
    fn mixed32(&mut self) -> [u8; 32] {
        if self.below(3) == 0 {
            self.structured32()
        } else {
            self.bytes32()
        }
    }
}

// ---------------------------------------------------------------------------------------
// Getting bytes into and out of a vector
// ---------------------------------------------------------------------------------------

/// A `Vec256` holding the given 32 bytes, least significant first.
#[target_feature(enable = "avx2")]
fn v256_of(bytes: &[u8; 32]) -> Vec256 {
    let mut elems = [0i16; 16];
    for (k, e) in elems.iter_mut().enumerate() {
        *e = i16::from_le_bytes([bytes[2 * k], bytes[2 * k + 1]]);
    }
    load_i16(&elems, 0)
}

/// The 32 bytes of a `Vec256`, least significant first.
#[target_feature(enable = "avx2")]
fn v256_bytes(v: Vec256) -> [u8; 32] {
    let mut elems = [0i16; 16];
    store_i16(&mut elems, 0, v);
    let mut out = [0u8; 32];
    for (k, e) in elems.iter().enumerate() {
        out[2 * k..2 * k + 2].copy_from_slice(&e.to_le_bytes());
    }
    out
}

/// A `Vec128` holding the given 16 bytes, least significant first.
#[target_feature(enable = "avx2")]
fn v128_of(bytes: &[u8; 16]) -> Vec128 {
    load_u8x16(bytes, 0)
}

/// The 16 bytes of a `Vec128`, least significant first.
#[target_feature(enable = "avx2")]
fn v128_bytes(v: Vec128) -> [u8; 16] {
    let wide = v256_bytes(broadcastsi128_si256(v));
    let mut out = [0u8; 16];
    out.copy_from_slice(&wide[..16]);
    out
}

// ---------------------------------------------------------------------------------------
// Record emission
// ---------------------------------------------------------------------------------------

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(2 * bytes.len());
    for b in bytes {
        s.push(char::from_digit((b >> 4) as u32, 16).unwrap());
        s.push(char::from_digit((b & 0xF) as u32, 16).unwrap());
    }
    s
}

/// One `.jsonl` line.  Fields are written in a fixed order so the file is byte-reproducible;
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
        match $imm { $( $n => $f::<$n> $args, )* _ => unreachable!() }
    };
}

/// Patterns worth trying before the random ones: saturation boundaries, sign-bit boundaries,
/// the all-set control byte `vpshufb` reads as "zero this lane", and plain counting.
fn edge_cases() -> Vec<[u8; 32]> {
    let rep = |pat: [u8; 4]| -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, b) in out.iter_mut().enumerate() {
            *b = pat[i % 4];
        }
        out
    };
    let mut counting = [0u8; 32];
    for (i, b) in counting.iter_mut().enumerate() {
        *b = i as u8;
    }
    let mut descending = [0u8; 32];
    for (i, b) in descending.iter_mut().enumerate() {
        *b = 31 - i as u8;
    }
    std::vec![
        [0u8; 32],
        [0xFF; 32],
        rep([0x00, 0x80, 0x00, 0x80]), // i16::MIN in every 16-bit lane
        rep([0xFF, 0x7F, 0xFF, 0x7F]), // i16::MAX in every 16-bit lane
        rep([0x00, 0x00, 0x00, 0x80]), // i32::MIN in every 32-bit lane
        rep([0xFF, 0xFF, 0xFF, 0x7F]), // i32::MAX in every 32-bit lane
        rep([0x01, 0x00, 0xFF, 0xFF]), // +1 / -1 alternating 16-bit lanes
        counting,
        descending,
    ]
}

// ---------------------------------------------------------------------------------------
// The vectors
// ---------------------------------------------------------------------------------------

/// Runs every wrapper over the fixed input set and returns the `.jsonl` contents.
#[target_feature(enable = "avx2")]
fn build() -> String {
    let mut rng = Rng(SEED);
    let mut o = String::with_capacity(8 << 20);
    let edges = edge_cases();

    // --- two-argument lane operations -------------------------------------------------
    //
    // Each is exercised on every ordered pair of edge patterns and then on `N_RANDOM` random
    // pairs.  `$name` is both the wrapper and the string the Lean runner dispatches on.
    macro_rules! binop {
        ($name:ident) => {{
            let mut run = |a: [u8; 32], b: [u8; 32]| {
                let r = v256_bytes($name(v256_of(&a), v256_of(&b)));
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
                run(rng.mixed32(), rng.mixed32());
            }
        }};
    }

    binop!(and_si256);
    binop!(add_epi16);
    binop!(sub_epi16);
    binop!(add_epi32);
    binop!(sub_epi32);
    binop!(mullo_epi16);
    binop!(mulhi_epi16);
    binop!(mullo_epi32);
    binop!(cmpgt_epi32);
    binop!(srlv_epi32);
    binop!(shuffle_epi8);
    binop!(unpacklo_epi16);
    binop!(unpackhi_epi16);
    binop!(unpacklo_epi32);
    binop!(unpackhi_epi32);
    binop!(unpacklo_epi64);
    binop!(unpackhi_epi64);
    binop!(packs_epi32);
    binop!(packus_epi32);

    // --- shifts by an immediate --------------------------------------------------------
    //
    // The immediate is drawn uniformly from its whole range rather than pinned, so all of
    // them are covered several dozen times each; the axioms quantify over it.
    macro_rules! shift {
        ($name:ident, $bound:expr, [$($n:literal),*]) => {{
            let mut run = |a: [u8; 32], imm: i32| {
                let r = v256_bytes(imm_call!(imm, $name, (v256_of(&a)), [$($n),*]));
                Rec::new(stringify!($name))
                    .hex("a", &a)
                    .num("imm", imm as i64)
                    .hex("o", &r)
                    .emit(&mut o);
            };
            for a in &edges {
                for imm in 0..$bound {
                    run(*a, imm);
                }
            }
            for _ in 0..N_RANDOM {
                let imm = rng.below($bound as u64) as i32;
                run(rng.mixed32(), imm);
            }
        }};
    }

    shift!(
        srai_epi16,
        16,
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    );
    shift!(
        srli_epi16,
        16,
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    );
    #[rustfmt::skip]
    shift!(srai_epi32, 32, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
                            16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]);
    #[rustfmt::skip]
    shift!(slli_epi32, 32, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
                            16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]);

    // --- `vpsrlw` by a register --------------------------------------------------------
    //
    // The count is the whole low 64 bits of the second operand, so counts far above the lane
    // width (which must shift the lane out entirely rather than wrap) are part of the claim.
    {
        let mut run = |a: [u8; 32], c: [u8; 16]| {
            let r = v256_bytes(srl_epi16(v256_of(&a), v128_of(&c)));
            Rec::new("srl_epi16")
                .hex("a", &a)
                .hex("c", &c)
                .hex("o", &r)
                .emit(&mut o);
        };
        for a in &edges {
            for count in 0..20u64 {
                let mut c = [0u8; 16];
                c[..8].copy_from_slice(&count.to_le_bytes());
                run(*a, c);
            }
        }
        for _ in 0..N_RANDOM {
            // Mostly small counts, but a full-width one now and then for the "shifts
            // everything out" case.
            let mut c = [0u8; 16];
            let count = if rng.below(4) == 0 {
                rng.u64()
            } else {
                rng.below(20)
            };
            c[..8].copy_from_slice(&count.to_le_bytes());
            run(rng.mixed32(), c);
        }
    }

    // --- cross-half permutes -----------------------------------------------------------
    //
    // Only the immediates the backend uses, plus enough others to exercise both selector
    // fields and `vperm2i128`'s zeroing bit, which the backend never sets but the axiom
    // claims.
    {
        const P2: [i32; 12] = [
            0x20, 0x31, 0x00, 0x11, 0x02, 0x13, 0x08, 0x80, 0x88, 0x30, 0x21, 0x23,
        ];
        for &imm in P2.iter() {
            let mut run = |a: [u8; 32], b: [u8; 32]| {
                #[rustfmt::skip]
                let r = v256_bytes(imm_call!(imm, permute2x128_si256, (v256_of(&a), v256_of(&b)),
                    [0x20, 0x31, 0x00, 0x11, 0x02, 0x13, 0x08, 0x80, 0x88, 0x30, 0x21, 0x23]));
                Rec::new("permute2x128_si256")
                    .hex("a", &a)
                    .hex("b", &b)
                    .num("imm", imm as i64)
                    .hex("o", &r)
                    .emit(&mut o);
            };
            for a in &edges {
                run(*a, edges[1]);
            }
            for _ in 0..(N_RANDOM / P2.len()) {
                run(rng.mixed32(), rng.mixed32());
            }
        }

        const P4: [i32; 12] = [
            0xD8, 0x4B, 0x00, 0xFF, 0x1B, 0xE4, 0x4E, 0x93, 0x27, 0x6C, 0xB1, 0x39,
        ];
        for &imm in P4.iter() {
            let mut run = |a: [u8; 32]| {
                #[rustfmt::skip]
                let r = v256_bytes(imm_call!(imm, permute4x64_epi64, (v256_of(&a)),
                    [0xD8, 0x4B, 0x00, 0xFF, 0x1B, 0xE4, 0x4E, 0x93, 0x27, 0x6C,
                     0xB1, 0x39]));
                Rec::new("permute4x64_epi64")
                    .hex("a", &a)
                    .num("imm", imm as i64)
                    .hex("o", &r)
                    .emit(&mut o);
            };
            for a in &edges {
                run(*a);
            }
            for _ in 0..(N_RANDOM / P4.len()) {
                run(rng.mixed32());
            }
        }
    }

    // --- half-register moves -----------------------------------------------------------
    {
        let mut run = |a: [u8; 32]| {
            for imm in 0..2i32 {
                let r = v128_bytes(imm_call!(imm, extracti128_si256, (v256_of(&a)), [0, 1]));
                Rec::new("extracti128_si256")
                    .hex("a", &a)
                    .num("imm", imm as i64)
                    .hex("o", &r)
                    .emit(&mut o);
            }
            let r = v128_bytes(castsi256_si128(v256_of(&a)));
            Rec::new("castsi256_si128")
                .hex("a", &a)
                .hex("o", &r)
                .emit(&mut o);
        };
        for a in &edges {
            run(*a);
        }
        for _ in 0..N_RANDOM {
            run(rng.mixed32());
        }
    }

    {
        let mut run = |a: [u8; 16]| {
            let r = v256_bytes(cvtepu16_epi32(v128_of(&a)));
            Rec::new("cvtepu16_epi32")
                .hex("a", &a)
                .hex("o", &r)
                .emit(&mut o);
            let r = v256_bytes(broadcastsi128_si256(v128_of(&a)));
            Rec::new("broadcastsi128_si256")
                .hex("a", &a)
                .hex("o", &r)
                .emit(&mut o);
        };
        for a in &edges {
            let mut half = [0u8; 16];
            half.copy_from_slice(&a[..16]);
            run(half);
        }
        for _ in 0..N_RANDOM {
            run(rng.bytes16());
        }
    }

    // --- constants ---------------------------------------------------------------------
    {
        for &v in &[0i16, 1, -1, i16::MIN, i16::MAX, 0x1234, -0x1234] {
            let r = v256_bytes(set1_epi16(v));
            Rec::new("set1_epi16")
                .hex("a", &v.to_le_bytes())
                .hex("o", &r)
                .emit(&mut o);
        }
        for _ in 0..N_RANDOM {
            let v = rng.u64() as i16;
            let r = v256_bytes(set1_epi16(v));
            Rec::new("set1_epi16")
                .hex("a", &v.to_le_bytes())
                .hex("o", &r)
                .emit(&mut o);
        }
        for &v in &[0i32, 1, -1, i32::MIN, i32::MAX, 0x1234_5678, -0x1234_5678] {
            let r = v256_bytes(set1_epi32(v));
            Rec::new("set1_epi32")
                .hex("a", &v.to_le_bytes())
                .hex("o", &r)
                .emit(&mut o);
            let r = v128_bytes(cvtsi32_si128(v));
            Rec::new("cvtsi32_si128")
                .hex("a", &v.to_le_bytes())
                .hex("o", &r)
                .emit(&mut o);
        }
        for _ in 0..N_RANDOM {
            let v = rng.u64() as i32;
            let r = v256_bytes(set1_epi32(v));
            Rec::new("set1_epi32")
                .hex("a", &v.to_le_bytes())
                .hex("o", &r)
                .emit(&mut o);
            let r = v128_bytes(cvtsi32_si128(v));
            Rec::new("cvtsi32_si128")
                .hex("a", &v.to_le_bytes())
                .hex("o", &r)
                .emit(&mut o);
        }
        Rec::new("setzero_si256")
            .hex("o", &v256_bytes(setzero_si256()))
            .emit(&mut o);
    }

    // --- memory ------------------------------------------------------------------------
    //
    // The buffers are dumped whole, in memory order, so that the recorded vector pins both
    // the offset arithmetic and — for the `*_of_*` accessors — the little-endian
    // reinterpretation of a wide element array as a narrow one.
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
                let r = v256_bytes($name(&buf, idx));
                Rec::new(stringify!($name))
                    .hex("buf", &raw)
                    .num("idx", idx as i64)
                    .hex("o", &r)
                    .emit(&mut o);
            }
        }};
    }

    load_test!(load_i16, i16, 64, 16);
    load_test!(load_u16, u16, 64, 16);
    load_test!(load_i32, i32, 32, 8);
    load_test!(load_u8, u8, 128, 32);
    // The two-blocks-in-one-buffer views: `[i32; 32]` read as 64 `i16`, `[i64; 16]` as 32 `i32`.
    load_test!(load_i16_of_i32, i32, 32, 8);
    load_test!(load_i32_of_i64, i64, 16, 4);

    // `load_u8x16` is byte-indexed rather than vector-indexed, so it gets its own loop.
    for _ in 0..N_MEMORY {
        let mut raw = [0u8; 64];
        rng.fill(&mut raw);
        let off = rng.below(49) as usize;
        let r = v128_bytes(load_u8x16(&raw, off));
        Rec::new("load_u8x16")
            .hex("buf", &raw)
            .num("idx", off as i64)
            .hex("o", &r)
            .emit(&mut o);
    }

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
                let val = rng.bytes32();
                $name(&mut buf, idx, v256_of(&val));
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

    store_test!(store_i16, i16, 64, 16);
    store_test!(store_u16, u16, 64, 16);
    store_test!(store_i16_of_i32, i32, 32, 8);
    store_test!(store_i32_of_i64, i64, 16, 4);

    o
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

/// The path the Lean runner reads.
fn vectors_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/intrinsics_vectors.jsonl")
}

/// Anchors the read-back path: `set1_epi16` fixes the bytes of every lane without any load
/// being involved, so this fails if `store_i16` has the byte order wrong — which a
/// `load`-then-`store` round trip could not detect on its own.
#[test]
fn readback_byte_order() {
    if !super::available() {
        return;
    }
    // SAFETY: guarded by the `available()` check above.
    unsafe {
        assert_eq!(v256_bytes(set1_epi16(0x1234)), [0x34, 0x12].repeat(16)[..]);
        assert_eq!(
            v256_bytes(set1_epi32(0x1234_5678)),
            [0x78, 0x56, 0x34, 0x12].repeat(8)[..]
        );
        assert_eq!(v128_bytes(cvtsi32_si128(0x0A0B_0C0D)), {
            let mut want = [0u8; 16];
            want[..4].copy_from_slice(&[0x0D, 0x0C, 0x0B, 0x0A]);
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
    // SAFETY: guarded by the `available()` check above.
    let produced = unsafe { build() };
    let path = vectors_path();

    if std::env::var_os("KOPIS_REGEN_VECTORS").is_some() {
        std::fs::write(&path, &produced).expect("writing intrinsics_vectors.jsonl");
        return;
    }

    let committed = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        std::panic!(
            "{}: {e}\nrun `KOPIS_REGEN_VECTORS=1 cargo test --lib intrinsics_vectors` to create it",
            path.display()
        )
    });
    assert!(
        committed == produced,
        "tests/intrinsics_vectors.jsonl disagrees with this CPU ({} vs {} bytes). \
         Either the wrappers changed or the recorded vectors are stale.",
        committed.len(),
        produced.len()
    );
}
