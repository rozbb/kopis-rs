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

Hashing is a path again on AVX2. `src/backend/avx2/keccak.rs` runs four independent TurboSHAKE
sponges side by side, one per 64-bit lane, which is the shape Kopis samples in: the public
matrix is ℓ² independent XOF calls differing only in a two-byte index, and the secret is ℓ
more. Serial and NEON builds, and every other TurboSHAKE call in the crate, still go through the
[`turboshake`](https://crates.io/crates/turboshake) crate. The four-way version is checked
against it byte for byte by `keccak::test::matches_scalar`.

This module is opaque to the extraction — it names `core::arch` intrinsics directly instead of
going through `intrinsics`, so the AVX2 row of the proofs assumes it rather than translating it.
See the *Formal Verification* section.

By default there is nothing to configure: on x86 targets both backends are compiled and the
AVX2 one is selected at first use by a CPUID check, so the binary still runs on machines
without AVX2. On every other target only the serial backend exists.

The choice can be forced with the `kopis_backend` cfg:

```sh
# portable only: no unsafe, no runtime dispatch
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

That table is the shipped configuration, which does *not* include the four-way TurboSHAKE. Its
effect, measured separately on an i9-12900H with `./bench.sh auto` (which adds alignment flags,
so its absolute numbers sit a little above the table's), is not uniform:

| operation        | `turboshake` crate | four-way | change |
| ---------------- | -----------------: | -------: | -----: |
| kopis512 keygen  |               9.93 |     8.89 | −10.5% |
| kopis512 encap   |               3.44 |     3.95 | **+15.0%** |
| kopis512 decap   |               5.96 |     6.19 |  +3.9% |
| kopis768 keygen  |              16.99 |    16.00 |  −5.8% |
| kopis768 encap   |               4.84 |     4.65 |  −4.0% |
| kopis768 decap   |               8.27 |     8.04 |  −2.8% |
| kopis1024 keygen |              26.29 |    22.55 | −14.2% |
| kopis1024 encap  |               5.98 |     6.02 |  +0.6% |
| kopis1024 decap  |              10.41 |    10.57 |  +1.5% |

Key generation is where it pays: that is the operation which expands the ℓ×ℓ matrix, so there
are ℓ² independent sponges to fill the lanes with and the batch is always full. Encapsulation
is the opposite case — it generates no matrix at all (the public key already carries `A` in NTT
form), so its only XOF work is the ℓ-element secret, and a four-lane batch run for ℓ = 2 does
twice the permutations it needs. That is the +15% on kopis512. At ℓ = 4 the lanes are all used
and encapsulation still does not improve, which is the more telling result: per lane, this
permutation is not faster than the one in the `turboshake` crate, and the wins above come from
batching rather than from the vectorization being better code.

One caveat on the kopis768 row: µ = 8 there, and the shipped code sends only the widths that
straddle byte boundaries through the AVX2 `cbd`. So that row moves the sampler onto the vector
path as well as the XOF, and its encap/decap gains are not attributable to the XOF alone. The
kopis512 (µ = 10) and kopis1024 (µ = 6) rows use the AVX2 `cbd` in both columns and are clean
comparisons.

# Formal Verification

We use [aeneas](https://github.com/AeneasVerif/aeneas) to extract our Rust implementation to Lean. After making changes to the Rust, run `extract_rust_to_lean.sh`, which regenerates `lean/ExtractedRustSerial.lean`.

The extraction covers the serial backend only — the script sets `--cfg kopis_backend="serial"`,
which removes the AVX2 dispatch before the compiler sees the crate, so what is extracted is
exactly the portable code. The AVX2 backend is held to the same behaviour by tests that compare
it against the serial code operation by operation, rather than by the proofs.

Where the AVX2 backend *is* extracted, `extract_rust_to_lean.sh` keeps three of its modules
opaque, which aeneas turns into axioms: `intrinsics` (the instruction set), `cpu` (the CPUID
probe), and now `backend::avx2::keccak` (the four-way TurboSHAKE). The third is a real widening
of the trust base rather than a bookkeeping one — `xof4` is the XOF that feeds both samplers,
and opaque means nothing is proved about the bytes it returns. It is held only by
`keccak::test::matches_scalar`, which checks it against the `turboshake` crate.

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
