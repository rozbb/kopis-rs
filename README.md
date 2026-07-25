# kopis-rs

This crate is a pure-Rust, no-std implementation of the Kopis key encapsulation mechanism (KEM). Kopis is a lattice-based KEM that is designed to be secure against classical and quantum adversaries. It comes in three variants:

* Kopis-512, which is designed to have security roughly equivalent to AES-128
* Kopis-768, which is designed to have security roughly equivalent to AES-192
* Kopis-1024, which is designed to have security roughly equivalent to AES-256

# Example code

The following code can be found in [`examples/simple.rs`](examples/simple.rs).

```rust
use kopis::{
    kopis512::{Kopis512Ciphertext, Kopis512PublicKey, Kopis512SecretKey, KOPIS512_CIPHERTEXT_LEN},
    SharedSecret
};

let mut rng = rand::rng();

// Generate a keypair
let sk = Kopis512SecretKey::generate(&mut rng);
let pk = sk.public_key();

// Serialize the secret key, maybe to save on disk
let sk_seed: &[u8; 32] = sk.seed();

// Deserialize the secret key
let sk = Kopis512SecretKey::expand_from_seed(sk_seed);

// Also serialize and deserialize the public key
let mut pk_bytes = [0u8; Kopis512PublicKey::SERIALIZED_LEN];
pk.serialize(&mut pk_bytes);
let slice_containing_pk = pk_bytes.as_slice();
assert_eq!(
    slice_containing_pk.len(),
    Kopis512PublicKey::SERIALIZED_LEN
);
let pk_arr = slice_containing_pk.try_into().unwrap();
// The API only accepts fixed-len slices, so we have to cast it first
let pk = Kopis512PublicKey::from_bytes(pk_arr);

// Encapsulate a shared secret, ss1, to pk
let (ct, ss1): (Kopis512Ciphertext, SharedSecret) = pk.encapsulate(&mut rng);
// Note ct is just a [u8; KOPIS512_CIPHERTEXT_LEN]

// Deserializing is also straightforward
let slice_containing_ct = ct.as_slice();
let receiver_ct: &Kopis512Ciphertext = slice_containing_ct.try_into().unwrap();

// Use the secret key to decapsulate the ciphertext
let ss2 = sk.decapsulate(receiver_ct);

// Check the shared secrets are equal. NOTE is not a constant-time check (ie not secure). We
// only do this for testing purposes.
assert_eq!(ss1.as_bytes(), ss2.as_bytes());

println!("KEM ran successfully");
```

# Benchmarks

We have implemented benchmarks for key generation, encapsulation, and decapsulation for all variants. Simply run `cargo bench`.

# Backends

The crate ships two implementations of its arithmetic. The **serial** backend is portable
`no_std` Rust with no `unsafe` anywhere; it is the reference, and the one the Lean proofs are
about. The **avx2** backend is an x86-64/x86 rewrite of the hot paths — the negacyclic NTT, the
bit-packing, and the binomial sampler — that computes bit-identical results, checked against the
serial code by tests in each module.

Hashing is not among those paths. Every TurboSHAKE invocation, in both backends, goes through
the [`turboshake`](https://crates.io/crates/turboshake) crate; this crate contains no Keccak
implementation of its own and no vectorized substitute for one.

By default there is nothing to configure: on x86 targets both backends are compiled and the
AVX2 one is selected at first use by a CPUID check, so the binary still runs on machines
without AVX2. On every other target only the serial backend exists.

The choice can be forced with the `kopis_backend` cfg:

```sh
# portable only: no unsafe, no runtime dispatch, and what gets extracted to Lean
RUSTFLAGS='--cfg kopis_backend="serial"' cargo build

# AVX2 unconditionally, with no runtime check and no fallback
RUSTFLAGS='--cfg kopis_backend="avx2"' cargo build
```

`avx2` makes the build script verify that AVX2 really is available for the target — the target
must be x86, and either `avx2` must be in the enabled target features (`-C target-feature=+avx2`,
`-C target-cpu=native`) or the build must be a native one on a CPU that reports AVX2. If it is
not, the build fails with an explanatory panic rather than producing a binary that would fault
at run time.

On a 12th-generation Intel Core (`cargo bench`, microseconds, lower is better):

| operation           | serial | avx2  | speedup |
| ------------------- | -----: | ----: | ------: |
| kopis512 keygen     |  20.3  |  8.5  |   2.4× |
| kopis512 encap      |  12.1  |  3.6  |   3.4× |
| kopis512 decap      |  19.1  |  6.0  |   3.2× |
| kopis768 keygen     |  35.0  | 14.8  |   2.4× |
| kopis768 encap      |  15.9  |  4.5  |   3.6× |
| kopis768 decap      |  24.4  |  8.0  |   3.1× |
| kopis1024 keygen    |  54.6  | 23.8  |   2.3× |
| kopis1024 encap     |  21.1  |  6.3  |   3.4× |
| kopis1024 decap     |  31.1  | 10.4  |   3.0× |

Key generation gains least because it is the operation that spends the most of its time inside
the XOF, which is untouched.

# Formal Verification

We use [aeneas](https://github.com/AeneasVerif/aeneas) to extract our Rust implementation to Lean. After making changes to the Rust, run `extract_rust_to_lean.sh`, which regenerates `lean/ExtractedRust.lean`.

The extraction covers the serial backend only — the script sets `--cfg kopis_backend="serial"`,
which removes the AVX2 dispatch before the compiler sees the crate, so what is extracted is
exactly the portable code. The AVX2 backend is held to the same behaviour by tests that compare
it against the serial code operation by operation, rather than by the proofs.

That extracted code is then proved to match an audited Lean specification of Kopis. The proofs live in [`lean/`](lean/); see [`lean/README.md`](lean/README.md) for the layout. To check them:

```sh
cd lean
make prove-kopis      # build + kernel-verify the correspondence proofs
make test-kopis-spec  # run the audited spec against the Kopis test vectors
```

# License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE))
 * MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
