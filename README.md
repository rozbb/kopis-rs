# kopis-rs

This crate is a pure-Rust, no-std implementation of the Kopis key encapsulation mechanism (KEM). Kopis is a lattice-based KEM that is designed to be secure against classical and quantum adversaries. It comes in three variants:

* Kopis-512, which is designed to have security roughly equivalent to AES-128
* Kopis-768, which is designed to have security roughly equivalent to AES-192
* Kopis-1024, which is designed to have security roughly equivalent to AES-256

# Example code

The following code can be found in [`examples/simple.rs`](examples/simple.rs).

```rust
use kopis::{
    SharedSecret,
    kopis768::{
        KOPIS768_CIPHERTEXT_LEN, KOPIS768_PUBKEY_LEN, Kopis768Ciphertext, Kopis768PublicKey,
        Kopis768SecretKey,
    },
    subtle::ConstantTimeEq,
};

# fn main() {
let mut rng = rand::rng();

// Alice generates a keypair
let sk = Kopis768SecretKey::generate_from_rng(&mut rng);
let pk = sk.public_key();

// Alice serializes the secret key, and saves to disk
let sk_seed = sk.seed();

// Alice serializes her pubkey and sends to bob
let _pk_bytes = pk.to_bytes();
let pk_bytes = _pk_bytes.as_slice();

// Bob receives the public key and deserializes
// The API only accepts fixed-len slices, so we have to cast it first
let pk_arr: &[u8; KOPIS768_PUBKEY_LEN] = pk_bytes.try_into().unwrap();
let pk = Kopis768PublicKey::from_bytes(pk_arr);

// Bob encapsulates to Alice and gets a shared secret ss1
let (_ct, ss1): (Kopis768Ciphertext, SharedSecret) = pk.encapsulate_with_rng(&mut rng);
let ct = _ct.as_slice();

// Alice receives the ciphertext. She reconstructs her decap key from her saved seed
let sk = Kopis768SecretKey::from_seed(sk_seed);
let ct_arr: &[u8; KOPIS768_CIPHERTEXT_LEN] = ct.try_into().unwrap();
let ss2 = sk.decapsulate(ct_arr);

// Check the shared secrets are equal
assert!(bool::from(ss1.ct_eq(&ss2)));

println!("KEM ran successfully");
# }
```

# Benchmarks

We have implemented benchmarks for key generation, encapsulation, and decapsulation for all variants. Simply run `cargo bench`.

# Backends

The crate ships two implementations of its arithmetic. The **serial** backend is portable
`no_std` Rust with no `unsafe` anywhere; it is the reference. The **avx2** backend is an x86-64/x86 rewrite of the hot paths — the negacyclic NTT, the
bit-packing, and the binomial sampler; the **neon** backend does the same on AArch64. The
bit-packing and the sampler compute bit-identical results, checked against the serial code by
tests (the sampler directly in its own module; the bit-packing through the shared
deserialization tests, which dispatch to the vector backend on hardware that has it).

The NTT is the exception, and it is now the exception everywhere. All three implementations —
serial included — transform over two 16-bit primes and recombine by the CRT rather than using a
single 26-bit prime. On the vector backends the reason is that neither vector unit's 32-bit
multiply is as cheap as its 16-bit one. On the serial backend the reason is the same one seen
from the other side: "portable" does not mean "scalar", because LLVM auto-vectorizes the
butterfly loops, and baseline SSE2 has no 64-bit multiply for the single-prime product to use —
it has to emulate it, while the 16-bit butterfly is one `pmullw` and one `pmulhw` over eight
lanes. Switching the serial backend to two primes made its forward transform 1.68× faster and
its inverse 2.40× faster, which is 20–45% off every serial KEM operation. The scheme, its
constants and its correctness argument live in `src/backend/crt.rs`; the portable
implementation is `src/arithmetic/ntt_crt.rs`.

These transforms compute the same ring products as the single-prime one, and are tested against
it directly (`crt_matches_single`, `avx2_matches_serial`, `neon_matches_serial`), against
schoolbook multiplication over all three parameter sets, and by the KATs. But their intermediate
values are different integers, so the Lean correspondence proof — which is about the
single-prime transform in `src/arithmetic/ntt.rs` — does not extend to them. Since that
transform no longer ships in any configuration (it is retained as a `#[cfg(test)]` reference,
precisely to be the oracle for `crt_matches_single`), **the proofs do not currently cover the
ring multiplication in any build**. Re-establishing that coverage means porting the proof to the
two-prime transform; there is no longer a build configuration that gets it for free.

Hashing is a path on both vector backends. `src/backend/avx2/keccak.rs` runs four independent
TurboSHAKE sponges side by side, one per 64-bit lane, which is the shape Kopis samples in: the
public matrix is ℓ² independent XOF calls differing only in a two-byte index, and the secret is
ℓ more. `src/backend/neon/keccak.rs` is the two-way counterpart, narrower only because a
`uint64x2_t` holds two 64-bit lanes to a `Vec256`'s four — which also wastes fewer lanes on the
batch sizes Kopis uses, since ℓ = 2 fills a two-lane batch exactly.

The NEON version is written against the ARMv8.2 SHA3 extension, whose four instructions are
Keccak steps rather than general bit tricks (`eor3` for θ's column fold, `rax1` for its
neighbour mixing, `xar` for θ's per-lane xor fused with ρ's rotation, `bcax` for χ), and that is
what makes it worth doing: scalar AArch64 gets its rotates free in the second operand, so a
plain-NEON two-way permutation does not clearly beat two scalar sponges. Since that is the bulk
of what the backend buys, the extension is a requirement for the **whole** NEON backend rather
than for this file alone: `build.rs` compiles it only when the target has both `neon` and
`sha3` — `aarch64-apple-darwin` has both by default — and an AArch64 target without the
extension gets the portable serial backend instead. There is therefore exactly one NEON
configuration to build, test, and prove. The decision is made at build time rather than by a
runtime probe because the crate is `no_std` and `core` has no AArch64 feature detection.

Serial builds — which is what AArch64 targets without the extension get — and every other
TurboSHAKE call in the crate still go through the
[`turboshake`](https://crates.io/crates/turboshake) crate. Both
batched versions are checked against it byte for byte by `keccak::test::matches_scalar`, and the
batched samplers against the definition of the XOF by `gen_matrix_matches_definition` and
`gen_secret_matches_definition`.

Both are also covered by the proofs: `xof4` and `xof2` are each proved to be TurboSHAKE, against
the same FIPS 202 specification, so they rest on more than their tests. See the *Formal
Verification* section.

By default there is nothing to configure: on x86 targets both backends are compiled and the
AVX2 one is selected at first use by a CPUID check, so the binary still runs on machines
without AVX2. On AArch64 targets that enable `neon` and `sha3` with a hardfloat ABI the NEON
backend is compiled in and always used, since both features are confirmed at build time. On
every other target only the serial backend exists.

The choice can be forced with the `kopis_backend` cfg:

```sh
# portable only: no unsafe, no runtime dispatch
RUSTFLAGS='--cfg kopis_backend="serial"' cargo build

# AVX2 unconditionally, with no runtime check and no fallback
RUSTFLAGS='--cfg kopis_backend="avx2"' cargo build

# likewise NEON; needs +sha3, which aarch64-apple-darwin has by default
RUSTFLAGS='--cfg kopis_backend="neon"' cargo build
```

`avx2` makes the build script verify that AVX2 really is available for the target — the target
must be x86, and either `avx2` must be in the enabled target features (`-C target-feature=+avx2`,
`-C target-cpu=native`) or the build must be a native one on a CPU that reports AVX2. `neon`
does the same for AArch64: the target must enable both `neon` and `sha3` and must not use the
softfloat ABI. If the check fails, the build fails with an explanatory panic rather than
producing a binary that would fault at run time.

# Constant-Time Checking

Every secret-dependent branch and every secret-dependent memory address is a timing side channel,
so `ct-check.sh` looks for both. It tags the crate's secret inputs as *undefined* memory using
Valgrind's client requests, then runs the public API under Memcheck. Memcheck already reports
"conditional jump depends on uninitialised value" and "address depends on uninitialised value",
and under this tagging those are exactly the two leak shapes. Definedness propagates bit-precisely
through arithmetic, so masks, rotations and `subtle`'s constant-time selects stay silent no matter
how much secret data flows through them.

It needs Valgrind and its headers:

```bash
sudo apt install valgrind        # Debian/Ubuntu
sudo dnf install valgrind valgrind-devel
```

```bash
# every operation, every parameter set, on the backend this machine would normally build
./ct-check.sh

# pin a backend, or narrow to one operation or parameter set
./ct-check.sh --backend serial
./ct-check.sh --variant 768 decap

# prove the harness can still see a leak at all (runs deliberately leaky code; must FAIL to be
# silent). Worth running whenever the harness or the toolchain changes.
./ct-check.sh --selftest
```

Three operations are covered. **Decapsulation** is the important one — it is the oracle a
chosen-ciphertext attacker gets to query — and it is checked with the whole expanded secret key
tagged and the ciphertext left public, since the attacker chooses that. It runs against a
well-formed ciphertext, a one-bit-corrupted one, and an unstructured one, so that both sides of
the implicit-rejection comparison are exercised. **Encapsulation** tags the encapsulation
randomness, and **key generation** tags the 32-byte seed. All of them are clean today, with no
suppressions: kopis samples the public matrix by deserialising 13-bit coefficients rather than by
rejection, so there is no intentional leak to whitelist the way a mod-3329 scheme would need.

**Backend coverage is limited by the host.** Valgrind interprets the guest's own instruction set,
so there is no cross-architecture option: a backend can only be checked on hardware that runs it.
On an x86-64 machine that means `serial` and `avx2`, which is what CI does. **`neon` is checked
only if you run the script on AArch64 hardware with FEAT_SHA3** — Apple silicon, or Neoverse
V-series; Neoverse N1 (Graviton2) lacks the extension, and macOS has no arm64 Valgrind port, so in
practice this means Linux on AArch64. The script refuses up front rather than pretending
otherwise. Until someone runs it there, the NEON Keccak and NTT are covered by the equivalence
tests and the Lean proofs but *not* by this check.

Two caveats are worth stating plainly. Memcheck only sees the path that actually ran, so a leak
in a branch these inputs never take goes unreported; that is why each check drives several
distinct inputs. And it says nothing about leaks below the instruction level — a variable-latency
multiplier, or a data-dependent microarchitectural effect — only about branches and addresses.
What it does give, on the code it did run, is soundness: it works on the executed instruction
stream, so it covers the hand-written AVX2 and NEON intrinsics as thoroughly as the portable
Rust, and it cannot be fooled by an optimiser turning a select into a branch after the fact.

The harness lives in `ct-check/`, kept out of the main crate so that the `unsafe` its client
requests need does not weaken kopis's own `forbid(unsafe_code)`.

# Formal Verification

We use [aeneas](https://github.com/AeneasVerif/aeneas) to extract our Rust implementation to Lean. After making changes to the Rust, run `extract_rust_to_lean.sh`, which regenerates the three
extracted files.

**All three backends are extracted and proved.** The script runs the extraction once per
backend, forcing `kopis_backend` each time so that each run sees exactly one set of dispatch
blocks: `lean/ExtractedRustSerial.lean` (the portable code), `lean/ExtractedRustAvx2.lean`, and
`lean/ExtractedRustNeon.lean`. Both vector backends are cross-extractions against a named
target — `x86_64-unknown-linux-gnu` with `-C target-feature=+avx2`, and
`aarch64-unknown-linux-gnu` with `-C target-feature=+sha3` — rather than against whatever host
happens to run the script. Each of the three is proved to satisfy the same nine top-level
theorems, so the vector backends are held by the proofs and not merely by the differential
tests.

What stays opaque — and therefore becomes an assumption rather than a definition — is the
instruction set, plus AVX2's CPUID probe:

* `backend::avx2::intrinsics` and `backend::neon::intrinsics`, whose semantics are supplied by
  hand in `lean/Kopis/Avx2/Intrinsics.lean` and `lean/Kopis/Neon/Intrinsics.lean`. Those two
  files are the whole of what each backend adds to the trust base, and both are *tested against
  real silicon*: each axiom is proved to pin its operation down to a computable model, and those
  models are replayed against input/output pairs recorded by executing the real instructions
  (`make test-avx2-model`, `make test-neon-model`).
* `backend::avx2::cpu`, the CPUID/XGETBV probe. NEON needs no counterpart: it is baseline on
  AArch64, so `available()` extracts as a compile-time `true`.

The four-way and two-way TurboSHAKE are *not* opaque — `xof4` and `xof2` are both proved to be
TurboSHAKE against FIPS 202.

That extracted code is then proved to match an audited Lean specification of Kopis. The proofs live in [`lean/`](lean/); see [`lean/README.md`](lean/README.md) for the layout, and
[`lean/TrustBase.lean`](lean/TrustBase.lean) for the enumerated assumptions of each backend. To check them:

```sh
cd lean
make prove-kopis      # build + kernel-verify the correspondence proofs, all three backends
make test-kopis-spec  # run the audited spec against the Kopis test vectors
make test-avx2-model  # replay recorded silicon vectors through the AVX2 intrinsic models
make test-neon-model  # the same for NEON
```

## Dependencies

Checking the proofs and re-running the extraction have *different* requirements, and only the
first is something most people need. The extracted `.lean` files are committed, so you can check
every proof without ever running charon.

### To check the proofs

* **[elan](https://github.com/leanprover/elan)**, the Lean toolchain manager. Do not install Lean
  by hand: `lean/lean-toolchain` pins `leanprover/lean4:v4.31.0` and elan honours it
  automatically.
* **A checkout of [aeneas](https://github.com/AeneasVerif/aeneas)'s Lean backend** as a *sibling*
  of this repository, so that `../../aeneas/backends/lean` resolves from `lean/`. Adjust the path
  in `lean/lakefile.lean` and `lean/lake-manifest.json` if yours lives elsewhere.

  **Use revision `b59d5188` — this tree does not build against aeneas `main`.** aeneas is a
  *path* dependency, so no revision is recorded in the manifest, and the same SHA appears as
  `AENEAS_VERSION` in `extract_rust_to_lean.sh`. The next commit upstream, `e30579c0`, adds
  `@[step]`-tagged shift lemmas that make `step*` overshoot in three of our proofs. See the setup
  section of [`lean/NEON_VERIFICATION_PLAN.md`](lean/NEON_VERIFICATION_PLAN.md) for the symptoms.
* **Mathlib's build cache.** Run `lake exe cache get` from `lean/` before the first build;
  compiling Mathlib from source instead costs hours.
* **Memory.** Each Lean worker holds ~1.75 GB resident. The `Makefile` caps parallelism at
  `LEAN_NUM_THREADS=8`; lower it on a small host (`make prove-kopis LEAN_NUM_THREADS=2`) or the
  build will swap-thrash.

No Rust toolchain, and no nix, are needed for any of this.

### To re-run the extraction

Only needed after changing the Rust. `extract_rust_to_lean.sh` pins the toolchain by SHA and
fetches it through nix, so nothing has to be installed by hand:

* **[nix](https://nixos.org/download/)**. The script passes `--extra-experimental-features
  nix-command --extra-experimental-features flakes` itself, so flakes need not be enabled in your
  `nix.conf`. The first run builds charon and aeneas from source, which is slow.
* **rustup, and the two targets the vector extractions cross-compile to:**

  ```sh
  rustup target add x86_64-unknown-linux-gnu   # AVX2
  rustup target add aarch64-unknown-linux-gnu  # NEON
  ```

  Both vector backends name their target explicitly rather than building for the host, so the
  extraction is the same on every machine and the script runs anywhere — including Apple
  silicon, where an AVX2 build for the *host* is impossible. The AVX2 block also passes
  `-C target-feature=+avx2`, which is what makes `build.rs` accept the configuration for a cross
  build: the host-CPU fallback it would otherwise use is disabled as soon as host and target
  differ.

### To re-record the intrinsic vectors

Both vector files are committed, so `make test-avx2-model` and `make test-neon-model` run
anywhere. Regenerating them means *executing* the instructions, so each needs its own host:

```sh
# on an AVX2 x86-64 machine
KOPIS_REGEN_VECTORS=1 cargo test --lib intrinsics_vectors

# on an AArch64 machine with FEAT_SHA3 (any Apple silicon Mac)
RUSTFLAGS='-C target-feature=+sha3' KOPIS_REGEN_VECTORS=1 \
  cargo test --lib neon::intrinsics_vectors
```

A plain `cargo test` on either host re-checks the committed file against that CPU, so drift is
caught continuously.

# License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE))
 * MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
