# Kopis formal verification

Machine-checked proof that the `kopis-rs` Rust implementation matches an
audited, executable specification of the Kopis KEM.

The chain has three links:

```
  ../src/*.rs        charon + aeneas       ExtractedRust.lean       Kopis/Properties/*.lean
  (Rust impl)   ──────────────────────▶   (extracted Lean)   ◀──────────────────────────▶   Spec/Kopis/Spec.lean
                 ../extract_rust_to_lean.sh                    correspondence proofs          (audited spec)
```

Nothing in `Kopis/Properties/` is trusted: `lake` type-checks it all, and the
Lean kernel re-checks every proof term. What *is* trusted is (a) the audited
spec in `Spec/`, which you should read against `kopis-spec.md`, and (b) the
charon/aeneas extraction that produced `ExtractedRust.lean` from the Rust.

## Usage

```sh
make prove-kopis      # lake build Kopis — build + kernel-verify all proofs
make test-kopis-spec  # lake exe kopisTests — run the spec against test vectors
```

Run both from this directory: `test-kopis-spec` reads its vectors from
`SpecTests/Kopis/vectors/` relative to the current directory.

`make prove-kopis` succeeding *is* the proof — a green build means every
theorem checked, with no `sorry`s and no errors.

## Layout

| Path                   | Trusted? | Contents                                                                                       |
| ---------------------- | -------- | ---------------------------------------------------------------------------------------------- |
| `ExtractedRust.lean`   | trusted  | Aeneas output. **Generated — never edit.** Re-run `../extract_rust_to_lean.sh` instead.          |
| `Spec/Kopis/Spec.lean` | trusted  | The audited Kopis specification, transcribed from `kopis-spec.md`.                               |
| `Spec/TurboSHAKE/`     | trusted  | TurboSHAKE (RFC 9861), the XOF Kopis samples from. See `turboshake_rfc.txt`.                     |
| `Spec/SHA3/`           | trusted  | Keccak-p permutation (FIPS 202) that TurboSHAKE rides on.                                        |
| `Spec/Defs.lean`       | trusted  | Shared spec-level definitions (bit/byte conversions and friends).                                |
| `Kopis/Properties/`    | *proved* | The correspondence proofs: extracted code ≡ spec, bottom-up to keygen/encap/decap.               |
| `Kopis.lean`           | —        | Aggregator: importing it pulls in the whole proof closure. Target of `lake build Kopis`.         |
| `SpecTests/`           | —        | Runs the *spec* (not the Rust) against known-answer vectors, to catch spec transcription bugs.   |

## Dependencies

`lakefile.lean` requires [aeneas](https://github.com/AeneasVerif/aeneas)'s Lean
backend as a local path dependency at `../../aeneas/backends/lean`, i.e. aeneas
is expected to be checked out as a sibling of the `kopis-rs` checkout. Adjust
that path (in both `lakefile.lean` and `lake-manifest.json`) if yours lives
elsewhere. Everything else — Mathlib and its transitive dependencies — is
fetched by `lake`.
