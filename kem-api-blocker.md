# Why the `kem`-crate API is shelved

Status: **blocked on aeneas**, shelved 2026-09-24. Branch `use-kem-api`, commit `c1aeaba`
(prototype: RustCrypto `kem` 0.3 traits for Kopis-512).

## The blocker

Every `kem` type — `Key<Self>`, `Ciphertext<K>`, `SharedKey<K>` — is `hybrid_array::Array<u8, U>`,
whose length lives in a **GAT** (`ArraySize::ArrayType<T>`, hybrid-array/src/traits.rs:22). Aeneas
cannot lift GATs, so the extraction dies before emitting anything:

```
Error: Detected groups of mixed mutually recursive definitions:
  - type decl:  hybrid_array::Array
  - trait decl: hybrid_array::traits::ArraySize
  - trait decl: hybrid_array::traits::AssocArraySize
used at: {impl kem::Kem for NewKopis512},
         {impl KeySizeUser/KeyExport/KeyInit/TryKeyInit/Encapsulate for KemPublicKey<2>},
         {impl Decapsulator/Decapsulate for KemSecretKey<2>}
```

charon warns first: `GATs cannot work with --lift-associated-types (implied by --preset=aeneas).
Either stop using this option or --exclude this trait`.

Two smaller breakages the traits force, each independent of the above:

| Cause | Error |
|---|---|
| `Debug for KemPublicKey`/`PkePublicKey`, required by `Kem::EncapsulationKey: Debug`. `debug_struct().field()` goes through `&dyn Debug`, which charon's monomorphizer does not support | `Internal error, please file an issue` |
| `generate_inner` on `TryCryptoRng` with `R::Error` + `?`, required by `Generate` | `Assertion failed: new value doesn't have the same type as its destination` |

So CI's `rust-to-lean-extraction` job is already red on this branch.

## What was tried

Serial backend only, aeneas `nightly-2026.07.18-b59d518`, `charon cargo --preset=aeneas` then
`aeneas kopis.llbc -backend lean -loops-to-rec`.

* `--exclude hybrid_array::traits::ArraySize` (what charon's own warning suggests) — still fails.
* `--exclude` all of `hybrid_array` — still fails.
* `--exclude` `hybrid_array` + `crypto_common` + `kem` — still fails.

Each fails differently; none gets past it. charon's help notes a trait impl cannot be filtered,
only its methods.

## If we come back to this

Whatever the mechanism, the trait layer lands outside the verified boundary — `hybrid_array::Array`
cannot cross into Lean. So the `kem` traits can only ever be thin wrappers delegating to the
inherent `[u8; N]` methods the proofs target; they cannot be the whole API.

### Recommended: module placement + `--start-from`. No cfg, no feature.

1. Put the kem layer in one module (`impls::kem_api`): the trait impls *and* the
   `Debug`/`PartialEq`/`Eq` impls the traits require on `KemPublicKey`/`PkePublicKey`.
2. Root the extraction at what the proofs need, in `extract_rust_to_lean.sh`:
   `--start-from kopis::impls::kopis512 --start-from …768 --start-from …1024 --start-from kopis::kem`
3. Keep `generate_inner` infallible (`CryptoRng`); `Generate::try_generate_from_rng` does its own
   `try_fill_bytes` + `expand_from_seed` (as `kem_traits.diff` already did).
4. `pke_pk` and `hash_pke_pk` become `pub(crate)`, so the moved `Debug` impl can read them.

Verified on the serial backend: charon exit 0 with zero GAT warnings, aeneas exit 0 with zero
errors, no proof-referenced definition dropped, and the proof-facing bodies byte-identical to the
committed `ExtractedRustSerial.lean` (the only diff was a doc-comment line number my scratch edits
had shifted). The extracted file does pick up ~140 lines of `rand_core` 0.9 → 0.10 trait preamble
that `kem` 0.3 drags in; no proof references it. **Not verified:** `make prove-kopis` was never run,
so "the extracted file still elaborates" is an assumption.

Gotchas, each of which cost a round trip:

* `--start-from` roots must be modules. Naming a method inside one fails with `--start-from only
  supports impl patterns if they're the first element of the path`.
* The three variant modules alone are not enough: that drops `kem.KemSecretKey.impl.seed`, which
  `Kopis/Properties/KeyGen.lean`, `KeyGenCapstone.lean` (×3) and `TopLevelTheoremsSerial.lean:138`
  all reference. Hence the `kopis::kem` root.
* That root pulls in everything in `kopis::kem`, so the `Debug` impl cannot live there — which is
  why it moves to `kem_api` rather than merely being gated.
* Extraction is now reachability-bounded: a future proof about an item no root reaches would
  silently vanish from the output. CI regenerates and diffs the extraction, so it surfaces there.

### Alternatives

| Option | Cost |
|---|---|
| Cargo feature `kem-api`, default on; extract with `-- --no-default-features` | A user-facing knob, and `#[cfg(feature = "kem-api")]` on every gated item. Checkable with `cargo check --no-default-features`. |
| Bespoke `--cfg kopis_extracting` (verified working) | One `cargo::rustc-check-cfg` line in `build.rs` beside the existing five. Shipped code differs from extracted code in a way only the script knows. |
| Separate `kopis-kem` crate | No extraction changes at all, but the orphan rule forces newtype wrappers around every key type. |

## What a trait-only API would cost, even with GAT support

`TopLevelTheoremsSerial.lean` states `toBytes`/`fromBytes`/`decap` over `Array U8 672#usize` etc.;
under the trait API those become `hybrid_array.Array` wrappers. ~75 references to restate:
`TopLevelTheoremsSerial.lean` (15), `Kopis/Properties/Impls.lean` (27), `KeyGenCapstone.lean` (24),
`KemFromBytes.lean` (9), plus the AVX2/NEON twins.

## To unblock upstream

File against [AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas): GAT lifting for
`hybrid_array::traits::ArraySize`, and the two internal errors above (`dyn Debug` via
`debug_struct`, `TryCryptoRng`'s `R::Error` + `?`). The first is the one that matters; the other
two are avoidable by hand.
