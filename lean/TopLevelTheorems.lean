import Kopis

/-!
# Top-level theorems — the audit surface for `kopis-rs`

This file exists to be **read by a human**. Everything else in `Kopis/Properties/`
is machinery; this is the summary you have to agree with in order to believe the
claim "the `kopis-rs` Rust crate is formally verified".

Nothing here is re-proved. Every theorem below is discharged by handing back the
theorem proved elsewhere in the library, so a restatement that drifted from what
was actually proved would fail to compile. Reading this file is therefore
equivalent to reading the real statements, without reading the proofs.

## The claim, in one sentence

For every input, the Rust implementation of key generation, encapsulation and
decapsulation **terminates without panicking** and returns exactly what the
audited specification in `Spec/Kopis/Spec.lean` says it should.

## Reading guide: which world does a name come from?

Nothing is `open`ed in this file except the Aeneas framework itself (`Array`, `Slice`,
`U8`, `Usize`, `Result`, the `⦃ … ⦄` notation), which belongs to none of the three
worlds below. Every other name therefore carries a prefix saying what it is:

| prefix | world | status |
| ------ | ----- | ------ |
| `RustKopis.…` | the **extracted Rust** (`ExtractedRust.lean`, from `../src/*.rs`) | trusted |
| `Spec.…` | the **audited specification** (`Spec/Kopis/Spec.lean`) | trusted |
| `Properties.…` | the **translation layer** (`Kopis/Properties/`) | proved — see §2 |

`RustKopis.…` is trusted because the charon/aeneas extraction is; `Spec.…` because you have
read it against `kopis-spec.md` and `make test-kopis-spec` passes. `Properties.…` is
proved, but it is where a statement could be made vacuous, so §2 pins it down.

So `RustKopis.kem.KemSecretKey.expand_from_seed` is Rust, `Spec.Kopis.ExpandDecapKey` is the
specification it is claimed to implement, and `Properties.arrayToBytes` is the glue that
lets the two be compared. A theorem is a claim about the Rust exactly when a
`RustKopis.…` name appears to the left of its `⦃ … ⦄`.

The `RustKopis` name is not what the Rust crate is called — the crate is `kopis`. It is
imposed by `../extract_rust_to_lean.sh` via aeneas's `-namespace` flag, precisely so that
extracted names cannot be mistaken for Lean-side ones. (Without it the extracted
namespace would be `kopis`, one capital letter away from `Kopis`, this development.)

The proof files under `Kopis/Properties/` do *not* follow this convention — they `open`
everything, because they are dense tactic scripts where the terseness pays. This file is
the one written to be read.

## What you have to check by hand

The Lean kernel checks the proofs. It cannot check that the *statements* say
something meaningful, so these four things are on you:

1. **§2 — the translation layer.** The theorems relate Rust values to spec values
   through functions like `arrayToBytes`. If one of those quietly threw away
   information, the theorems would be true but vacuous. §2 pins down what each
   one does.
2. **§3 — the theorem statements.** That they really do cover the operations you
   care about, applied to arbitrary inputs.
3. **§4 — the trust base.** The nine assumptions this development makes, and why
   each is there. The build fails if this list ever changes.
4. **§5 — the gaps.** What is deliberately *not* covered.

Two things outside this file remain trusted no matter how carefully you read it:
the audited spec really does describe Kopis (check `Spec/Kopis/Spec.lean` against
`kopis-spec.md`, and note that `make test-kopis-spec` runs it against the test
vectors), and the charon/aeneas extraction really did produce `ExtractedRust.lean`
from `../src/*.rs`.
-/

-- Deliberately minimal: only the Aeneas framework is opened, so every name below
-- carries a prefix identifying which world it comes from (see the reading guide).
open Aeneas Aeneas.Std Result
open Spec (𝔹)

namespace Kopis.TopLevel

/-! ## §1. What the `⦃ … ⦄` notation asserts

Every theorem below has the shape `<rust computation> ⦃ (r : _) => <property of r> ⦄`.
That is Aeneas's total-correctness postcondition, and it is stronger than it
looks: aeneas compiles Rust into a `Result` monad whose failure cases are `fail`
(a panic — arithmetic overflow, array bounds violation, explicit `panic!`,
failed `assert!`) and `div` (nontermination). The postcondition is *false* for
both, so asserting it also asserts that neither happens.

The theorem below makes that explicit, and it is the reason no separate
"does not panic" claim is needed: it is already inside each theorem in §3, for
all inputs, with no side conditions. -/

/-- A `⦃ … ⦄` postcondition says the computation **succeeds** — no panic, no
overflow, no out-of-bounds access, no divergence — *and* its result satisfies the
stated property. -/
theorem triple_means_success {α : Type} {x : Result α} {p : α → Prop} (h : x ⦃ p ⦄) :
    ∃ v, x = ok v ∧ p v := by
  cases x with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => simp [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta] at h
  | div => simp [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta] at h

/-! ## §2. The translation layer

The Rust side and the spec side use different types, so the theorems are stated
modulo translation functions. These are the place where a "proof" could be made
to say nothing at all — e.g. a translation that mapped every key to the empty
list would make correspondence trivial. So each one is pinned down here.

There are only three, and they are all boring, which is the point. -/

/-- **`arrayToBytes` is byte-for-byte identity.** A Rust `[u8; n]` becomes the
spec's `𝔹 n` by mapping each `U8` to its bit-vector, in order. Nothing is
reordered, truncated, padded or reinterpreted — the underlying byte list is
preserved exactly.

This is the translation used for every seed, every ciphertext and every shared
secret in §3. -/
theorem arrayToBytes_is_identity {n : Usize} (a : Array U8 n) :
    (Properties.arrayToBytes a).toList = a.val.map (·.bv) :=
  Kopis.Properties.arrayToBytes_toList a

/-- **`skBytes` is `arrayToBytes` at length 32.** The secret seed translation is
the identity one above, with a length cast that changes no bytes. -/
theorem skBytes_is_identity (sk : Array U8 32#usize) :
    (Properties.skBytes sk).toList = sk.val.map (·.bv) :=
  Kopis.Properties.arrayToBytes_toList sk

/-! ### The public key translation, and why it is not question-begging

`pkStructBytes` is the one translation that is not the identity: a Rust
`PkePublicKey` is a *struct* (a matrix of polynomials plus a 32-byte seed), while
the spec's `pk` is a flat byte string. `pkStructBytes` declares the struct's
meaning to be `serialize(vec) ‖ matrix_seed`.

Taken alone that would be an assumption — we would be *defining* the struct to
mean whatever makes the theorems come out right. It is not an assumption,
because the Rust crate's own serializer is proved to emit exactly those bytes.
`pk_serialize_matches_translation` below is that link: whatever
`PkePublicKey::serialize` writes into the output buffer is precisely the spec
serialization of the vector followed by the matrix seed. So a caller who
serializes a public key and puts it on the wire transmits exactly the byte string
the spec calls `pk`. -/

/-- **The Rust public-key serializer emits exactly the bytes `pkStructBytes`
claims.** This is what makes the public-key translation honest rather than
circular. (The two hypotheses are shape side conditions: the output buffer has
the right length, and the serialized size fits in a `usize`.) -/
theorem pk_serialize_matches_translation {L : Usize} (self : RustKopis.pke.PkePublicKey L)
    (out_buf : Slice U8) (hlen : out_buf.val.length = L.val * 320 + 32)
    (hfit : L.val * 10 * 256 ≤ Usize.max) :
    RustKopis.pke.PkePublicKey.serialize self out_buf
      ⦃ (r : Slice U8) => r.length = L.val * (32 * 10) + 32 ∧
          r.val.map (·.bv)
            = (Spec.Kopis.PolyVector.serialize 10 (Properties.toVecN 10 self.vec)).toList
            ++ (Properties.arrayToBytes self.matrix_seed).toList ⦄ :=
  Kopis.Properties.pke_serialize_spec self out_buf hlen hfit

/-- **The Rust public-key parser reads back exactly what the spec reads.** The dual of
the theorem above: where `serialize` writes `pkStructBytes`, `from_bytes` recovers, from
an arbitrary byte string of the right length, precisely the three things the audited
spec's `PkeEncrypt` reads out of a public key — the 10-bit-decoded vector, the matrix
seed, and the matrix regenerated from that seed via `GenMat`.

Nothing constrains the *contents* of the input, so this covers arbitrary and
adversarially chosen encodings; and being a `⦃ … ⦄` triple it also says the parser never
panics on them. -/
theorem pk_from_bytes_matches_spec {L : Usize} (bytes : Slice U8)
    (hlen : bytes.length = 320 * L.val + 32)
    (hfit : L.val * 10 * 256 ≤ Usize.max) :
    RustKopis.pke.PkePublicKey.from_bytes L bytes
      ⦃ (pk : RustKopis.pke.PkePublicKey L) =>
          Properties.toVecN 10 pk.vec
            = Spec.Kopis.PolyVector.deserialize (ℓ := L.val) 10
                (Spec.slice (Properties.sliceToBytes bytes (320 * L.val + 32) hlen) 0
                  (32 * 10 * L.val) (by omega)) ∧
          Properties.matSeedBytes pk
            = Spec.slice (Properties.sliceToBytes bytes (320 * L.val + 32) hlen)
                (32 * 10 * L.val) 32 (by omega) ∧
          Properties.toMatrix13 pk.mat_a
            = Spec.Kopis.GenMat L.val (Properties.arrayToBytes pk.matrix_seed) ⦄ :=
  Kopis.Properties.pke_from_bytes_spec bytes hlen hfit

/-! ## §3. The theorems

Four operations × three parameter sets. Every one is **unconditional**: the only
arguments are the inputs themselves, there are no hypotheses to discharge and no
side conditions hiding a restricted input range. Read them as:

> for *all* seeds / ciphertexts / randomness, the Rust computation succeeds and
> its output equals the spec's.

The `2#usize`/`10#usize`-style literals are the Rust const generics `ℓ` and `μ`:
(2, 10) is Kopis-512, (3, 8) is Kopis-768, (4, 6) is Kopis-1024. -/

/-! ### §3.1 Key generation — `expand_from_seed` matches `ExpandDecapKey`

`KemSecretKey::expand_from_seed` is what `Kopis512SecretKey::expand_from_seed`
and (via a random seed) `Kopis512SecretKey::generate` call. Each of the four
fields of the resulting secret key is the corresponding component of the spec's
`ExpandDecapKey`: the secret vector, the implicit-rejection seed `z`, the
serialized public key, and its hash. The fifth conjunct records that the public
matrix `A` is the spec's `GenMat` of the matrix seed. -/

/-- **Kopis-512 key generation matches the spec.** -/
theorem kopis512_keygen (seed : Array U8 32#usize) :
    RustKopis.kem.KemSecretKey.expand_from_seed 2#usize 10#usize seed
      ⦃ (ksk : RustKopis.kem.KemSecretKey 2#usize) =>
          Properties.toVector13 ksk.pke_sk
            = (Spec.Kopis.ExpandDecapKey .Kopis_512 (Properties.skBytes seed)).1 ∧
          Properties.arrayToBytes ksk.z
            = (Spec.Kopis.ExpandDecapKey .Kopis_512 (Properties.skBytes seed)).2.1 ∧
          Properties.pkStructBytes ksk.pke_pk .Kopis_512 rfl
            = (Spec.Kopis.ExpandDecapKey .Kopis_512 (Properties.skBytes seed)).2.2.1 ∧
          Properties.arrayToBytes ksk.hash_pke_pk
            = (Spec.Kopis.ExpandDecapKey .Kopis_512 (Properties.skBytes seed)).2.2.2 ∧
          Properties.toMatrix13 ksk.pke_pk.mat_a
            = Spec.Kopis.GenMat 2 (Properties.arrayToBytes ksk.pke_pk.matrix_seed) ⦄ :=
  Kopis.Properties.expand_from_seed_spec 2#usize 10#usize seed .Kopis_512
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)

/-- **Kopis-768 key generation matches the spec.** -/
theorem kopis768_keygen (seed : Array U8 32#usize) :
    RustKopis.kem.KemSecretKey.expand_from_seed 3#usize 8#usize seed
      ⦃ (ksk : RustKopis.kem.KemSecretKey 3#usize) =>
          Properties.toVector13 ksk.pke_sk
            = (Spec.Kopis.ExpandDecapKey .Kopis_768 (Properties.skBytes seed)).1 ∧
          Properties.arrayToBytes ksk.z
            = (Spec.Kopis.ExpandDecapKey .Kopis_768 (Properties.skBytes seed)).2.1 ∧
          Properties.pkStructBytes ksk.pke_pk .Kopis_768 rfl
            = (Spec.Kopis.ExpandDecapKey .Kopis_768 (Properties.skBytes seed)).2.2.1 ∧
          Properties.arrayToBytes ksk.hash_pke_pk
            = (Spec.Kopis.ExpandDecapKey .Kopis_768 (Properties.skBytes seed)).2.2.2 ∧
          Properties.toMatrix13 ksk.pke_pk.mat_a
            = Spec.Kopis.GenMat 3 (Properties.arrayToBytes ksk.pke_pk.matrix_seed) ⦄ :=
  Kopis.Properties.expand_from_seed_spec 3#usize 8#usize seed .Kopis_768
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)

/-- **Kopis-1024 key generation matches the spec.** -/
theorem kopis1024_keygen (seed : Array U8 32#usize) :
    RustKopis.kem.KemSecretKey.expand_from_seed 4#usize 6#usize seed
      ⦃ (ksk : RustKopis.kem.KemSecretKey 4#usize) =>
          Properties.toVector13 ksk.pke_sk
            = (Spec.Kopis.ExpandDecapKey .Kopis_1024 (Properties.skBytes seed)).1 ∧
          Properties.arrayToBytes ksk.z
            = (Spec.Kopis.ExpandDecapKey .Kopis_1024 (Properties.skBytes seed)).2.1 ∧
          Properties.pkStructBytes ksk.pke_pk .Kopis_1024 rfl
            = (Spec.Kopis.ExpandDecapKey .Kopis_1024 (Properties.skBytes seed)).2.2.1 ∧
          Properties.arrayToBytes ksk.hash_pke_pk
            = (Spec.Kopis.ExpandDecapKey .Kopis_1024 (Properties.skBytes seed)).2.2.2 ∧
          Properties.toMatrix13 ksk.pke_pk.mat_a
            = Spec.Kopis.GenMat 4 (Properties.arrayToBytes ksk.pke_pk.matrix_seed) ⦄ :=
  Kopis.Properties.expand_from_seed_spec 4#usize 6#usize seed .Kopis_1024
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)

/-! ### §3.2 Encapsulation — key generation then encapsulate matches `KemEncap`

These state the composite operation a user actually performs: generate a secret
key from a seed, derive the public key, encapsulate to it. The result is the
spec's `KemEncap` applied to the spec's `SkToPk` of the same seed — so the two
halves agree about what the public key is, which is what makes the composition
meaningful rather than each half matching a different notion of "public key".

`encapsulate_deterministic` takes its randomness as an argument; the `encapsulate`
wrapper that draws from an RNG is discussed in §5.

**Watch the pair ordering.** Rust returns `(ciphertext, shared_secret)`; the spec's
`KemEncap` returns `(shared_secret, ciphertext)`. The two conventions are opposite, so
the postconditions below equate `ct` with the `.2` of the spec result and `ss` with the
`.1`. That crossover is deliberate, not a transposition slip. The binders are named
`ct`/`ss` rather than projected out of a single `r` precisely so the mismatch is visible
on the page. -/

/-- **Kopis-512: key-gen → public key → encapsulate matches `KemEncap`.** -/
theorem kopis512_keygen_then_encapsulate (seed randomness : Array U8 32#usize) :
    (do let ksk ← RustKopis.kem.KemSecretKey.expand_from_seed 2#usize 10#usize seed
        let kpk ← RustKopis.impls.kopis512.Kopis512SecretKey.public_key ksk
        RustKopis.impls.kopis512.Kopis512PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (ct : Array U8 736#usize) (ss : RustKopis.impls.SharedSecret) =>
          Properties.arrayToBytes ct
              = (Spec.Kopis.KemEncap .Kopis_512 ((Properties.arrayToBytes randomness).cast rfl)
                  (Spec.Kopis.SkToPk .Kopis_512 (Properties.skBytes seed))).2
          ∧ Properties.arrayToBytes ss
              = (Spec.Kopis.KemEncap .Kopis_512 ((Properties.arrayToBytes randomness).cast rfl)
                  (Spec.Kopis.SkToPk .Kopis_512 (Properties.skBytes seed))).1 ⦄ :=
  Kopis.Properties.kopis512_keygen_encap_spec seed randomness

/-- **Kopis-768: key-gen → public key → encapsulate matches `KemEncap`.** -/
theorem kopis768_keygen_then_encapsulate (seed randomness : Array U8 32#usize) :
    (do let ksk ← RustKopis.kem.KemSecretKey.expand_from_seed 3#usize 8#usize seed
        let kpk ← RustKopis.impls.kopis768.Kopis768SecretKey.public_key ksk
        RustKopis.impls.kopis768.Kopis768PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (ct : Array U8 1088#usize) (ss : RustKopis.impls.SharedSecret) =>
          Properties.arrayToBytes ct
              = (Spec.Kopis.KemEncap .Kopis_768 ((Properties.arrayToBytes randomness).cast rfl)
                  (Spec.Kopis.SkToPk .Kopis_768 (Properties.skBytes seed))).2
          ∧ Properties.arrayToBytes ss
              = (Spec.Kopis.KemEncap .Kopis_768 ((Properties.arrayToBytes randomness).cast rfl)
                  (Spec.Kopis.SkToPk .Kopis_768 (Properties.skBytes seed))).1 ⦄ :=
  Kopis.Properties.kopis768_keygen_encap_spec seed randomness

/-- **Kopis-1024: key-gen → public key → encapsulate matches `KemEncap`.** -/
theorem kopis1024_keygen_then_encapsulate (seed randomness : Array U8 32#usize) :
    (do let ksk ← RustKopis.kem.KemSecretKey.expand_from_seed 4#usize 6#usize seed
        let kpk ← RustKopis.impls.kopis1024.Kopis1024SecretKey.public_key ksk
        RustKopis.impls.kopis1024.Kopis1024PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (ct : Array U8 1472#usize) (ss : RustKopis.impls.SharedSecret) =>
          Properties.arrayToBytes ct
              = (Spec.Kopis.KemEncap .Kopis_1024 ((Properties.arrayToBytes randomness).cast rfl)
                  (Spec.Kopis.SkToPk .Kopis_1024 (Properties.skBytes seed))).2
          ∧ Properties.arrayToBytes ss
              = (Spec.Kopis.KemEncap .Kopis_1024 ((Properties.arrayToBytes randomness).cast rfl)
                  (Spec.Kopis.SkToPk .Kopis_1024 (Properties.skBytes seed))).1 ⦄ :=
  Kopis.Properties.kopis1024_keygen_encap_spec seed randomness

/-! ### §3.2b Receiving a public key — parse then encapsulate matches `KemEncap`

The theorems above start from a locally generated key. These start from a public key
*received as bytes*, which is what a caller does with a key off the wire: parse it with
`from_bytes`, then encapsulate to it. The result is the spec's `KemEncap` applied to
exactly those bytes.

Nothing constrains the input bytes beyond their length, so a malformed or
adversarially chosen public-key encoding is covered — and, this being a `⦃ … ⦄` triple,
the composite is also proved not to panic on one.

The `ct`/`ss` pair ordering is the same crossover noted in §3.2. -/

/-- **Kopis-512: parse a received public key, then encapsulate to it.** -/
theorem kopis512_from_bytes_then_encapsulate (pk_bytes : Array U8 672#usize)
    (randomness : Array U8 32#usize) :
    (do let kpk ← RustKopis.impls.kopis512.Kopis512PublicKey.from_bytes pk_bytes
        RustKopis.impls.kopis512.Kopis512PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (ct : Array U8 736#usize) (ss : RustKopis.impls.SharedSecret) =>
          Properties.arrayToBytes ct
              = (Spec.Kopis.KemEncap .Kopis_512 ((Properties.arrayToBytes randomness).cast rfl)
                  ((Properties.arrayToBytes pk_bytes).cast rfl)).2
          ∧ Properties.arrayToBytes ss
              = (Spec.Kopis.KemEncap .Kopis_512 ((Properties.arrayToBytes randomness).cast rfl)
                  ((Properties.arrayToBytes pk_bytes).cast rfl)).1 ⦄ :=
  Kopis.Properties.kopis512_from_bytes_encap_spec pk_bytes randomness

/-- **Kopis-768: parse a received public key, then encapsulate to it.** -/
theorem kopis768_from_bytes_then_encapsulate (pk_bytes : Array U8 992#usize)
    (randomness : Array U8 32#usize) :
    (do let kpk ← RustKopis.impls.kopis768.Kopis768PublicKey.from_bytes pk_bytes
        RustKopis.impls.kopis768.Kopis768PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (ct : Array U8 1088#usize) (ss : RustKopis.impls.SharedSecret) =>
          Properties.arrayToBytes ct
              = (Spec.Kopis.KemEncap .Kopis_768 ((Properties.arrayToBytes randomness).cast rfl)
                  ((Properties.arrayToBytes pk_bytes).cast rfl)).2
          ∧ Properties.arrayToBytes ss
              = (Spec.Kopis.KemEncap .Kopis_768 ((Properties.arrayToBytes randomness).cast rfl)
                  ((Properties.arrayToBytes pk_bytes).cast rfl)).1 ⦄ :=
  Kopis.Properties.kopis768_from_bytes_encap_spec pk_bytes randomness

/-- **Kopis-1024: parse a received public key, then encapsulate to it.** -/
theorem kopis1024_from_bytes_then_encapsulate (pk_bytes : Array U8 1312#usize)
    (randomness : Array U8 32#usize) :
    (do let kpk ← RustKopis.impls.kopis1024.Kopis1024PublicKey.from_bytes pk_bytes
        RustKopis.impls.kopis1024.Kopis1024PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (ct : Array U8 1472#usize) (ss : RustKopis.impls.SharedSecret) =>
          Properties.arrayToBytes ct
              = (Spec.Kopis.KemEncap .Kopis_1024 ((Properties.arrayToBytes randomness).cast rfl)
                  ((Properties.arrayToBytes pk_bytes).cast rfl)).2
          ∧ Properties.arrayToBytes ss
              = (Spec.Kopis.KemEncap .Kopis_1024 ((Properties.arrayToBytes randomness).cast rfl)
                  ((Properties.arrayToBytes pk_bytes).cast rfl)).1 ⦄ :=
  Kopis.Properties.kopis1024_from_bytes_encap_spec pk_bytes randomness

/-! ### §3.3 Decapsulation — key generation then decapsulate matches `KemDecap`

Note what is *not* assumed: the ciphertext `ek` is an arbitrary byte array, not
one produced by encapsulation. So this covers the adversarial case — malformed,
adversarially chosen and replayed ciphertexts included — and in particular the
implicit-rejection path, where a ciphertext that fails the re-encryption check
must yield the pseudorandom `z`-derived secret rather than an error or a leak. -/

/-- **Kopis-512: key-gen → decapsulate an arbitrary ciphertext matches `KemDecap`.** -/
theorem kopis512_keygen_then_decapsulate (seed : Array U8 32#usize) (ek : Array U8 736#usize) :
    (do let ksk ← RustKopis.kem.KemSecretKey.expand_from_seed 2#usize 10#usize seed
        RustKopis.impls.kopis512.Kopis512SecretKey.decapsulate ksk ek)
      ⦃ (r : RustKopis.impls.SharedSecret) =>
          Properties.arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_512 (Properties.skBytes seed)
                ((Properties.arrayToBytes ek).cast rfl) ⦄ :=
  Kopis.Properties.kopis512_keygen_decap_spec seed ek

/-- **Kopis-768: key-gen → decapsulate an arbitrary ciphertext matches `KemDecap`.** -/
theorem kopis768_keygen_then_decapsulate (seed : Array U8 32#usize) (ek : Array U8 1088#usize) :
    (do let ksk ← RustKopis.kem.KemSecretKey.expand_from_seed 3#usize 8#usize seed
        RustKopis.impls.kopis768.Kopis768SecretKey.decapsulate ksk ek)
      ⦃ (r : RustKopis.impls.SharedSecret) =>
          Properties.arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_768 (Properties.skBytes seed)
                ((Properties.arrayToBytes ek).cast rfl) ⦄ :=
  Kopis.Properties.kopis768_keygen_decap_spec seed ek

/-- **Kopis-1024: key-gen → decapsulate an arbitrary ciphertext matches `KemDecap`.** -/
theorem kopis1024_keygen_then_decapsulate (seed : Array U8 32#usize) (ek : Array U8 1472#usize) :
    (do let ksk ← RustKopis.kem.KemSecretKey.expand_from_seed 4#usize 6#usize seed
        RustKopis.impls.kopis1024.Kopis1024SecretKey.decapsulate ksk ek)
      ⦃ (r : RustKopis.impls.SharedSecret) =>
          Properties.arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_1024 (Properties.skBytes seed)
                ((Properties.arrayToBytes ek).cast rfl) ⦄ :=
  Kopis.Properties.kopis1024_keygen_decap_spec seed ek

/-! ## §4. The trust base

Everything in §3 rests on exactly the assumptions listed below, and the `run_cmd`
at the end of this section **fails the build if that list ever changes** — so this
section cannot silently rot. Beyond Lean's own three axioms, they fall into four
groups.

**(a) The `turboshake` crate (5 assumptions).** `turboshake` is an external
crates.io dependency, so aeneas has no Lean model of its body and axiomatizes its
stateful API. `hasher_default_spec`, `hasher_update_spec`, `hasher_finalize_spec`,
`reader_read136_spec` and `reader_read168_spec` (in `Kopis/Properties/GenMatrix.lean`)
say that this API implements RFC 9861 — i.e. that absorbing bytes and then reading
`n` bytes yields `Spec.TurboSHAKE.turboSHAKE128/256`. This is the single largest
assumption in the development, and discharging it would mean verifying the
`turboshake` crate itself. Note it is a *functional* claim only: nothing about
timing or memory behaviour.

**(b) The `subtle` crate (2 assumptions).** `conditional_select_array_u8_spec` and
`ct_eq_slice_u8_spec` (in `Kopis/Properties/SubtleModel.lean`) give the functional
meaning of `subtle`'s constant-time select and equality: select returns one of its
two arguments according to the choice bit, and `ct_eq` is byte equality. These are
what the implicit-rejection branch of decapsulation is proved against. Again
functional only — that these operations are *actually* constant-time is a claim
about compiled machine code and is out of scope for this development entirely.

**(c) `u8::count_ones` / `u32::count_ones` (2 assumptions).**
`U8.count_ones_spec` and `U32.count_ones_spec` give the meaning of Rust's popcount
intrinsics, which aeneas leaves opaque.

**(d) Lean-side.** `propext`, `Classical.choice` and `Quot.sound` are the standard
axioms of Lean's logic — every Mathlib development uses them, and they are
consistent. `Aeneas.Std.core.fmt.Formatter` is an opaque type standing in for
Rust's formatting machinery, which no proof reasons about. The `RustKopis.*` entries
are the opaque types and functions aeneas emits for the extern crates named in (a)
and (b) — they carry no logical content of their own.

One entry deserves singling out:
`Spec.testBit_byte_of_bools._native.native_decide.ax` comes from a `native_decide`
in `Spec/Defs.lean:380`, which discharges a small finite bit-manipulation fact by
*compiled evaluation* rather than kernel reduction. That means trusting the Lean
compiler and runtime for that one step, which is a strictly larger trust base than
the kernel alone. It is a 2⁸-case check about byte bit-extraction, not a
cryptographic claim, but it is a real (if small) hole and could be closed by
replacing `native_decide` with `decide`.

**Not present, deliberately:** there is no `sorryAx` in the list. If any proof in
the closure were incomplete, `sorryAx` would appear here and the check below would
fail. -/

/-! The check itself. It recomputes the axiom footprint of every theorem in §3 and
compares it against the audited list above. Any new assumption — including a
`sorry` anywhere in the dependency closure — breaks the build here rather than
passing unnoticed. -/

open Lean in
run_cmd do
  let audited : List String :=
    ["Aeneas.Std.core.fmt.Formatter",
     "Classical.choice",
     "Kopis.Properties.U32.count_ones_spec",
     "Kopis.Properties.U8.count_ones_spec",
     "Kopis.Properties.conditional_select_array_u8_spec",
     "Kopis.Properties.ct_eq_slice_u8_spec",
     "Kopis.Properties.hasher_default_spec",
     "Kopis.Properties.hasher_finalize_spec",
     "Kopis.Properties.hasher_update_spec",
     "Kopis.Properties.reader_read136_spec",
     "Kopis.Properties.reader_read168_spec",
     "Quot.sound",
     "_private.Spec.Defs.0.Spec.testBit_byte_of_bools._native.native_decide.ax_1_1",
     "RustKopis.Array.Insts.SubtleConditionallySelectable.conditional_select",
     "RustKopis.Slice.Insts.SubtleConstantTimeEq.ct_eq",
     "RustKopis.U8.Insts.SubtleConditionallySelectable.conditional_select",
     "RustKopis.U8.Insts.SubtleConstantTimeEq.ct_eq",
     "RustKopis.core.num.U32.count_ones",
     "RustKopis.core.num.U8.count_ones",
     "RustKopis.subtle.Choice",
     "RustKopis.turboshake.TurboShake",
     "RustKopis.turboshake.TurboShake.Insts.CoreDefaultDefault.default",
     "RustKopis.turboshake.TurboShake.Insts.DigestExtendableOutputTurboShakeReader.finalize_xof",
     "RustKopis.turboshake.TurboShake.Insts.DigestUpdate.update",
     "RustKopis.turboshake.TurboShakeReader",
     "RustKopis.turboshake.TurboShakeReader.Insts.DigestXofReader.read",
     "propext"]
  let topLevel : List Name :=
    [``kopis512_keygen, ``kopis768_keygen, ``kopis1024_keygen,
     ``kopis512_keygen_then_encapsulate, ``kopis768_keygen_then_encapsulate,
     ``kopis1024_keygen_then_encapsulate,
     ``kopis512_keygen_then_decapsulate, ``kopis768_keygen_then_decapsulate,
     ``kopis1024_keygen_then_decapsulate,
     ``pk_serialize_matches_translation, ``pk_from_bytes_matches_spec,
     ``kopis512_from_bytes_then_encapsulate, ``kopis768_from_bytes_then_encapsulate,
     ``kopis1024_from_bytes_then_encapsulate]
  let mut found : Array String := #[]
  for t in topLevel do
    for a in (← Lean.collectAxioms t) do
      let s := a.toString
      if !found.contains s then found := found.push s
  let unexpected := found.filter (fun a => !audited.contains a)
  let unused := audited.filter (fun a => !found.contains a)
  unless unexpected.isEmpty && unused.isEmpty do
    throwError "TRUST BASE CHANGED — §4 of this file is out of date.\n\
      New assumptions not in the audited list: {unexpected.toList}\n\
      Audited assumptions no longer used: {unused}"

/-! ## §5. What is *not* proved

A verification claim is only as useful as its boundary. This one does not cover:

**Randomness.** `Kopis512SecretKey::generate` and `Kopis512PublicKey::encapsulate`
draw from a caller-supplied `CryptoRng`. The theorems in §3 cover the deterministic
cores those wrappers call (`expand_from_seed`, `encapsulate_deterministic`) as
functions of the seed / randomness they are handed. Nothing here says anything
about the quality of the RNG, and nothing checks that the wrappers pass the random
bytes through faithfully.

**Nothing about public-key deserialization** — this gap is now closed, by
`pk_from_bytes_matches_spec` in §2 and the three parse-then-encapsulate theorems in
§3.2b.

**Trivial accessors.** `SecretKey::seed`, `SharedSecret::as_bytes` and similar
getters have no theorems.

**KEM correctness as a mathematical property.** Nothing here proves that
decapsulating a validly encapsulated ciphertext recovers the encapsulator's shared
secret. That is a property of the *specification*, not of the Rust, and it is not
proved anywhere in this development — it is only checked empirically, by
`make test-kopis-spec`, on the bundled test vectors.

**Side channels.** The `subtle` axioms in §4(b) fix only the *functional* meaning
of constant-time primitives. Nothing here rules out timing or cache leaks; those
are properties of compiled machine code, which is outside what a source-level
proof about Rust semantics can see.

**Memory zeroization.** No claim that secret material is wiped after use.

**The extraction and the spec themselves.** As noted at the top: that
`ExtractedRust.lean` faithfully reflects `../src/*.rs` is a property of
charon/aeneas, and that `Spec/Kopis/Spec.lean` faithfully reflects `kopis-spec.md`
is a matter for human review plus the KAT runner. -/

end Kopis.TopLevel
