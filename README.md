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

This crate supports three "backends": **Portable** (no special hardware necessary), **AVX2**, and **NEON + SHA3** (meaning it only executes if there is NEON with `+sha3` in the target features). By default, this crate will look at the target architecture, pick the right backend, and do CPU feature support testing as needed.

If you want to **force a specific backend** to be used, you can do so via CFG flags:
```sh
# portable only: no unsafe, no runtime dispatch
RUSTFLAGS='--cfg kopis_backend="serial"' cargo build

# AVX2 unconditionally, with no runtime check and no fallback
RUSTFLAGS='--cfg kopis_backend="avx2"' cargo build

# likewise NEON; needs +sha3, which aarch64-apple-darwin has by default
RUSTFLAGS='--cfg kopis_backend="neon"' cargo build
```

# Formal Verification

We formally verify that this Rust crate matches the Lean specification in [`lean/Spec/Kopis/Spec.lean`]. Specifically, we check that the public KEM API matches the spec, for all supported backends. See [`lean/TopLevelTheoremsSerial.lean`] to see the specific properties tested.

## What is not proved

Some details are outside our formalization:

1. Rust SIMD intrinsics are not currently supported by aeneas. Thus, we axiomatize them and use test vectors to ensure equivalence (see `src/backend/{neon,avx2}/intrinsics_vectors.rs`).
2. `turboshake` and `subtle` are dependencies, and thus cannot be directly extracted. We axiomatize their behavior using a TurboSHAKE Lean specification. We also have our own parallelized TurboSHAKE impl for AVX2, which we prove matches the Lean spec.
3. We cannot prove in Lean that anything operates in constant-time. For this, see "Checking for constant-time" below

You can regenerate the SIMD test vectors as follows:
```sh
# on an AVX2 x86-64 machine
KOPIS_REGEN_VECTORS=1 cargo test --lib intrinsics_vectors

# on an AArch64 machine with FEAT_SHA3 (any Apple silicon Mac)
RUSTFLAGS='-C target-feature=+sha3' KOPIS_REGEN_VECTORS=1 \
  cargo test --lib neon::intrinsics_vectors
```

A plain `cargo test` on either host re-checks the committed file against that CPU, so drift is
caught continuously.

## Transpiling Rust to Lean

In order to prove correctness of Rust, it must first be translated to Lean. This is already done for you, and stored in the `lean/ExtractedRust*.lean` files. But if you made code changes and want to re-transpile, then do as follows.

1. Install [nix](https://nixos.org/download/). This is so we can run aeneas.
2. Install [rustup](https://rustup.rs/) so we can compile Rust
3. Run `extract_rust_to_lean.sh`

## Running Lean

To verify the theorems, you need to build the Lean project. To do this, follow these steps:

1. Install [elan](https://github.com/leanprover/elan), the Lean toolchain manager
2. `cd lean`
3. Run `lake exe cache get`. This will fetch the Mathlib cache and reduce build times by a lot.
4. Run `make prove-kopis` to prove the top-level theorems and check that all axioms have been audited. This will take a while. If you want to increase the number of threads (default is 8), then run `make prove-kopis LEAN_NUM_THREAD=16` or whatever you want.
5. Extra: Run `make test-avx2-model` and `make test-neon-model` to run unit tests on the Lean formalizations of AVX2 and NEON SIMD instructions. aeneas doesn't know how to extract these, so we had to axiomatize them.

# Checking for constant-timeness

To ensure that we don't accidentally introduce timing side channels in the code, we perform two checks in `ct-check.sh`:

1. Run valgrind with memory tainting to see if any functions branch on secrets. This is done in `ct-check/src/main.rs`.
2. Compile the library and search the resulting binary for non-constant-time instructions. The list of non-constant-time instructions is in `ct-check/scan-instrs.py` (we make no guarantees for Cortex M3 and below). The list of known false positives is in `ct-check/instr-allowlist.txt`.

Note that macOS does not have a valgrind implementation we can use, so we cannot run this on Macs.

# License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE))
 * MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
