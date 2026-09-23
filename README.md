# kopis-rs

This crate is a pure-Rust, no-std implementation of the Kopis key encapsulation mechanism (KEM). Kopis is a lattice-based KEM that is designed to be secure against classical and quantum adversaries. Kopis has three security levels: Kopis-512, Kopis-768, and Kopis-1024. If you don't know what to use, just use Kopis-768.

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

fn main() {
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
}
```

# Benchmarks

We have implemented benchmarks for key generation, encapsulation, and decapsulation for all variants. Simply run `cargo bench`.

# Backend selection

This crate supports three backends:
* Portable — No special hardware necessary
* AVX2 — x86-64 CPUs with AVX2
* NEON — aarch64 CPUs with NEON _and also SHA3_ (meaning presence of `+sha3` in the target features)

By default, this crate will look at the target architecture, pick the right backend, and do CPU feature support testing as needed.

If you want to **force a specific backend** to be used, you can do so via CFG flags:
```sh
# portable only: no unsafe, no runtime dispatch
RUSTFLAGS='--cfg kopis_backend="serial"' cargo build

# AVX2 unconditionally, with no runtime check and no fallback
RUSTFLAGS='--cfg kopis_backend="avx2"' cargo build

# likewise NEON; needs +sha3, which aarch64-apple-darwin has by default
RUSTFLAGS='--cfg kopis_backend="neon"' cargo build
```

# Formal verification

We formally verify that this Rust crate matches the Lean specification in [`lean/Spec/Kopis/Spec.lean`](lean/Spec/Kopis/Spec.lean). Specifically, we check that the public KEM API matches the spec, for all supported backends. We use [aeneas](https://github.com/AeneasVerif/aeneas) to lift the Rust implementation to Lean.

Read [`lean/README.md`](lean/README.md) for more info on what is proved, what is not proved, and how to run proofs.

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
