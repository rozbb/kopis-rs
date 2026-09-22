import Kopis.Properties.KeyGenHyps
import Kopis.Properties.Impls
open Aeneas Aeneas.Std Result RustKopisSerial
open Spec (𝔹)
namespace Kopis.Properties
set_option maxHeartbeats 4000000

/-! ## Unconditional decapsulation for a key-gen output.

Composing `expand_from_seed_spec` (key-gen = `ExpandSecretKey`) with the hypothesis
discharges (`keygen_hpkvec/hpkmat/hpkh`) removes ALL the structural side-conditions from
the decapsulation wrappers: for a secret key produced by `expand_from_seed` from a seed,
`decapsulate` computes exactly `KemDecap` of that seed. -/

/-- **Kopis-512: key-gen then decapsulate matches `KemDecap` (fully unconditional).** -/
theorem kopis512_keygen_decap_spec (seed : Array U8 32#usize) (ek : Array U8 736#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 2#usize 10#usize seed
        impls.kopis512.KemSecretKey2.decapsulate ksk ek)
      ⦃ (r : kem.SharedSecret) =>
          arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_512 (skBytes seed) ((arrayToBytes ek).cast rfl) ⦄ := by
  let* ⟨ksk, S, hSfwd, hSvec, hSbnd, hz, hpkb, hhash,
        Am, hAfwd, hAmat, hAbnd, V, hVfwd, hVbnd, hVbytes⟩ ← expand_from_seed_spec 2#usize 10#usize seed .Kopis_512
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  exact kopis512_decapsulate_spec ksk ek (skBytes seed) (pkStructBytes ksk.kem_pk.pke_pk .Kopis_512 rfl)
    S hSfwd hSvec hSbnd hz hpkb
    V Am hVfwd hAfwd
    (keygen_hpkvec ksk.kem_pk.pke_pk V .Kopis_512 rfl (by decide) hVbytes) hVbnd
    (keygen_hpkmat ksk.kem_pk.pke_pk Am .Kopis_512 rfl (by decide) hAmat) hAbnd
    (keygen_hpkh ksk.kem_pk.pke_pk ksk.kem_pk.hash_pke_pk .Kopis_512 rfl (skBytes seed) hhash hpkb)

/-- **Kopis-768: key-gen then decapsulate matches `KemDecap` (fully unconditional).** -/
theorem kopis768_keygen_decap_spec (seed : Array U8 32#usize) (ek : Array U8 1088#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 3#usize 8#usize seed
        impls.kopis768.KemSecretKey3.decapsulate ksk ek)
      ⦃ (r : kem.SharedSecret) =>
          arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_768 (skBytes seed) ((arrayToBytes ek).cast rfl) ⦄ := by
  let* ⟨ksk, S, hSfwd, hSvec, hSbnd, hz, hpkb, hhash,
        Am, hAfwd, hAmat, hAbnd, V, hVfwd, hVbnd, hVbytes⟩ ← expand_from_seed_spec 3#usize 8#usize seed .Kopis_768
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  exact kopis768_decapsulate_spec ksk ek (skBytes seed) (pkStructBytes ksk.kem_pk.pke_pk .Kopis_768 rfl)
    S hSfwd hSvec hSbnd hz hpkb
    V Am hVfwd hAfwd
    (keygen_hpkvec ksk.kem_pk.pke_pk V .Kopis_768 rfl (by decide) hVbytes) hVbnd
    (keygen_hpkmat ksk.kem_pk.pke_pk Am .Kopis_768 rfl (by decide) hAmat) hAbnd
    (keygen_hpkh ksk.kem_pk.pke_pk ksk.kem_pk.hash_pke_pk .Kopis_768 rfl (skBytes seed) hhash hpkb)

/-- **Kopis-1024: key-gen then decapsulate matches `KemDecap` (fully unconditional).** -/
theorem kopis1024_keygen_decap_spec (seed : Array U8 32#usize) (ek : Array U8 1472#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 4#usize 6#usize seed
        impls.kopis1024.KemSecretKey4.decapsulate ksk ek)
      ⦃ (r : kem.SharedSecret) =>
          arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_1024 (skBytes seed) ((arrayToBytes ek).cast rfl) ⦄ := by
  let* ⟨ksk, S, hSfwd, hSvec, hSbnd, hz, hpkb, hhash,
        Am, hAfwd, hAmat, hAbnd, V, hVfwd, hVbnd, hVbytes⟩ ← expand_from_seed_spec 4#usize 6#usize seed .Kopis_1024
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  exact kopis1024_decapsulate_spec ksk ek (skBytes seed) (pkStructBytes ksk.kem_pk.pke_pk .Kopis_1024 rfl)
    S hSfwd hSvec hSbnd hz hpkb
    V Am hVfwd hAfwd
    (keygen_hpkvec ksk.kem_pk.pke_pk V .Kopis_1024 rfl (by decide) hVbytes) hVbnd
    (keygen_hpkmat ksk.kem_pk.pke_pk Am .Kopis_1024 rfl (by decide) hAmat) hAbnd
    (keygen_hpkh ksk.kem_pk.pke_pk ksk.kem_pk.hash_pke_pk .Kopis_1024 rfl (skBytes seed) hhash hpkb)

/-- `SkToPk` unfolds definitionally to the public-key component of `ExpandSecretKey`. Proved
here (cheaply, by `rfl`) *before* the local-irreducible attribute below, so the
`keygen_encap` composites can bridge the two forms by rewriting with this equation rather than
by a `whnf` that would unfold the huge spec term. -/
theorem skToPk_eq (p : Spec.Kopis.ParameterSet) (sk : 𝔹 32) :
    Spec.Kopis.SkToPk p sk = (Spec.Kopis.ExpandSecretKey p sk).2.2.1 := rfl

-- The three `keygen_encap_spec` composites below check the `keygen_hpk*` facts against
-- `encapsulate_deterministic_spec`'s expected types over the huge spec-level `KemEncap` /
-- `ExpandSecretKey` / `SkToPk` terms.  Making those three spec definitions *locally* irreducible
-- stops `whnf`/`kabstract` from unfolding them during elaboration — which is exactly what
-- otherwise blows up — while the proofs only ever touch them through `skToPk_eq` and the
-- already-compiled specs.  (The decapsulation capstones above are unaffected: this attribute
-- takes effect only from here onward in the file.)
attribute [local irreducible]
  Spec.Kopis.SkToPk Spec.Kopis.KemEncap Spec.Kopis.ExpandSecretKey

/-- Kopis-512 `public_key` (the impls wrapper) hands back the stored `kem_pk`. -/
theorem kopis512_public_key_spec (self : kem.KemSecretKey 2#usize) :
    impls.kopis512.KemSecretKey2.public_key self
      ⦃ (kpk : kem.KemPublicKey 2#usize) =>
          kpk.pke_pk = self.kem_pk.pke_pk ∧ kpk.hash_pke_pk = self.kem_pk.hash_pke_pk ⦄ := by
  unfold impls.kopis512.KemSecretKey2.public_key
  exact ⟨rfl, rfl⟩

/-- **Kopis-512: key-gen → derive public key → encapsulate matches `KemEncap` (unconditional).** -/
theorem kopis512_keygen_encap_spec (seed randomness : Array U8 32#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 2#usize 10#usize seed
        let kpk ← impls.kopis512.KemSecretKey2.public_key ksk
        impls.kopis512.KemPublicKey2.encapsulate_deterministic kpk randomness)
      ⦃ (r : Array U8 736#usize × kem.SharedSecret) =>
          arrayToBytes r.1 = (Spec.Kopis.KemEncap .Kopis_512 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_512 (skBytes seed))).2
          ∧ arrayToBytes r.2 = (Spec.Kopis.KemEncap .Kopis_512 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_512 (skBytes seed))).1 ⦄ := by
  let* ⟨ksk, S, hSfwd, hSvec, hSbnd, hz, hpkb, hhash,
        Am, hAfwd, hAmat, hAbnd, V, hVfwd, hVbnd, hVbytes⟩ ← expand_from_seed_spec 2#usize 10#usize seed .Kopis_512
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  let* ⟨kpk, hkvec, hkhash⟩ ← kopis512_public_key_spec ksk
  have hpk3 : pkStructBytes kpk.pke_pk .Kopis_512 rfl
      = Spec.Kopis.SkToPk .Kopis_512 (skBytes seed) := by
    rw [hkvec, skToPk_eq]; exact hpkb
  let* ⟨r, hc, hk⟩ ← kopis512_encapsulate_deterministic_spec kpk randomness
    (pkStructBytes kpk.pke_pk .Kopis_512 rfl)
    V Am (by rw [hkvec]; exact hVfwd) (by rw [hkvec]; exact hAfwd)
    (keygen_hpkvec kpk.pke_pk V .Kopis_512 rfl (by decide) (by rw [hkvec]; exact hVbytes))
    hVbnd
    (keygen_hpkmat kpk.pke_pk Am .Kopis_512 rfl (by decide) (by rw [hkvec]; exact hAmat))
    hAbnd
    (keygen_hpkh kpk.pke_pk kpk.hash_pke_pk .Kopis_512 rfl (skBytes seed) (by rw [hkhash]; exact hhash)
      (by rw [hkvec]; exact hpkb))
  -- Bridge `pkStructBytes … = SkToPk …` *through* the opaque `KemEncap` head with `congrArg`,
  -- so the enormous spec term is never `whnf`'d (which is what made the old `rw`/`generalize`
  -- version heartbeat-pathological).  `KemEncap` stays an opaque function symbol throughout.
  have hE := congrArg (Spec.Kopis.KemEncap .Kopis_512 ((arrayToBytes randomness).cast rfl)) hpk3
  exact ⟨hc.trans (congrArg Prod.snd hE), hk.trans (congrArg Prod.fst hE)⟩

/-- Kopis-768 `public_key` (the impls wrapper) hands back the stored `kem_pk`. -/
theorem kopis768_public_key_spec (self : kem.KemSecretKey 3#usize) :
    impls.kopis768.KemSecretKey3.public_key self
      ⦃ (kpk : kem.KemPublicKey 3#usize) =>
          kpk.pke_pk = self.kem_pk.pke_pk ∧ kpk.hash_pke_pk = self.kem_pk.hash_pke_pk ⦄ := by
  unfold impls.kopis768.KemSecretKey3.public_key
  exact ⟨rfl, rfl⟩

/-- **Kopis-768: key-gen → derive public key → encapsulate matches `KemEncap` (unconditional).** -/
theorem kopis768_keygen_encap_spec (seed randomness : Array U8 32#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 3#usize 8#usize seed
        let kpk ← impls.kopis768.KemSecretKey3.public_key ksk
        impls.kopis768.KemPublicKey3.encapsulate_deterministic kpk randomness)
      ⦃ (r : Array U8 1088#usize × kem.SharedSecret) =>
          arrayToBytes r.1 = (Spec.Kopis.KemEncap .Kopis_768 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_768 (skBytes seed))).2
          ∧ arrayToBytes r.2 = (Spec.Kopis.KemEncap .Kopis_768 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_768 (skBytes seed))).1 ⦄ := by
  let* ⟨ksk, S, hSfwd, hSvec, hSbnd, hz, hpkb, hhash,
        Am, hAfwd, hAmat, hAbnd, V, hVfwd, hVbnd, hVbytes⟩ ← expand_from_seed_spec 3#usize 8#usize seed .Kopis_768
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  let* ⟨kpk, hkvec, hkhash⟩ ← kopis768_public_key_spec ksk
  have hpk3 : pkStructBytes kpk.pke_pk .Kopis_768 rfl
      = Spec.Kopis.SkToPk .Kopis_768 (skBytes seed) := by
    rw [hkvec, skToPk_eq]; exact hpkb
  let* ⟨r, hc, hk⟩ ← kopis768_encapsulate_deterministic_spec kpk randomness
    (pkStructBytes kpk.pke_pk .Kopis_768 rfl)
    V Am (by rw [hkvec]; exact hVfwd) (by rw [hkvec]; exact hAfwd)
    (keygen_hpkvec kpk.pke_pk V .Kopis_768 rfl (by decide) (by rw [hkvec]; exact hVbytes))
    hVbnd
    (keygen_hpkmat kpk.pke_pk Am .Kopis_768 rfl (by decide) (by rw [hkvec]; exact hAmat))
    hAbnd
    (keygen_hpkh kpk.pke_pk kpk.hash_pke_pk .Kopis_768 rfl (skBytes seed) (by rw [hkhash]; exact hhash)
      (by rw [hkvec]; exact hpkb))
  have hE := congrArg (Spec.Kopis.KemEncap .Kopis_768 ((arrayToBytes randomness).cast rfl)) hpk3
  exact ⟨hc.trans (congrArg Prod.snd hE), hk.trans (congrArg Prod.fst hE)⟩

/-- Kopis-1024 `public_key` (the impls wrapper) hands back the stored `kem_pk`. -/
theorem kopis1024_public_key_spec (self : kem.KemSecretKey 4#usize) :
    impls.kopis1024.KemSecretKey4.public_key self
      ⦃ (kpk : kem.KemPublicKey 4#usize) =>
          kpk.pke_pk = self.kem_pk.pke_pk ∧ kpk.hash_pke_pk = self.kem_pk.hash_pke_pk ⦄ := by
  unfold impls.kopis1024.KemSecretKey4.public_key
  exact ⟨rfl, rfl⟩

/-- **Kopis-1024: key-gen → derive public key → encapsulate matches `KemEncap` (unconditional).** -/
theorem kopis1024_keygen_encap_spec (seed randomness : Array U8 32#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 4#usize 6#usize seed
        let kpk ← impls.kopis1024.KemSecretKey4.public_key ksk
        impls.kopis1024.KemPublicKey4.encapsulate_deterministic kpk randomness)
      ⦃ (r : Array U8 1472#usize × kem.SharedSecret) =>
          arrayToBytes r.1 = (Spec.Kopis.KemEncap .Kopis_1024 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_1024 (skBytes seed))).2
          ∧ arrayToBytes r.2 = (Spec.Kopis.KemEncap .Kopis_1024 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_1024 (skBytes seed))).1 ⦄ := by
  let* ⟨ksk, S, hSfwd, hSvec, hSbnd, hz, hpkb, hhash,
        Am, hAfwd, hAmat, hAbnd, V, hVfwd, hVbnd, hVbytes⟩ ← expand_from_seed_spec 4#usize 6#usize seed .Kopis_1024
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  let* ⟨kpk, hkvec, hkhash⟩ ← kopis1024_public_key_spec ksk
  have hpk3 : pkStructBytes kpk.pke_pk .Kopis_1024 rfl
      = Spec.Kopis.SkToPk .Kopis_1024 (skBytes seed) := by
    rw [hkvec, skToPk_eq]; exact hpkb
  let* ⟨r, hc, hk⟩ ← kopis1024_encapsulate_deterministic_spec kpk randomness
    (pkStructBytes kpk.pke_pk .Kopis_1024 rfl)
    V Am (by rw [hkvec]; exact hVfwd) (by rw [hkvec]; exact hAfwd)
    (keygen_hpkvec kpk.pke_pk V .Kopis_1024 rfl (by decide) (by rw [hkvec]; exact hVbytes))
    hVbnd
    (keygen_hpkmat kpk.pke_pk Am .Kopis_1024 rfl (by decide) (by rw [hkvec]; exact hAmat))
    hAbnd
    (keygen_hpkh kpk.pke_pk kpk.hash_pke_pk .Kopis_1024 rfl (skBytes seed) (by rw [hkhash]; exact hhash)
      (by rw [hkvec]; exact hpkb))
  have hE := congrArg (Spec.Kopis.KemEncap .Kopis_1024 ((arrayToBytes randomness).cast rfl)) hpk3
  exact ⟨hc.trans (congrArg Prod.snd hE), hk.trans (congrArg Prod.fst hE)⟩

/-! ## Discharge lemmas for the audit surface

`TopLevelTheoremsSerial.lean` states its theorems and hands each straight back to a lemma; these
are the ones it hands back to that have no other home. -/

/-- **A `⦃ … ⦄` triple means the computation succeeds and its result satisfies the
postcondition.** -/
theorem triple_means_success {α : Type} {x : Result α} {p : α → Prop} (h : x ⦃ p ⦄) :
    ∃ v, x = ok v ∧ p v := by
  cases x with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => simp [WP.spec, WP.theta] at h
  | div => simp [WP.spec, WP.theta] at h

/-- **Generate a key, serialize its public key, get the spec's `pk`.**  `expand_from_seed_spec`
pins the struct's abstract serialization `pkStructBytes` to the spec's `pk`; `pke_serialize_spec`
says the crate's serializer writes exactly that pairing of bytes.  Composing them removes
`pkStructBytes` from the claim, leaving Rust bytes against spec bytes. -/
private theorem keygen_serialize_aux {L MU : Usize} {p : Spec.Kopis.ParameterSet}
    (seed : Array U8 32#usize) (out_buf : Slice U8) (hℓ : Spec.Kopis.ℓ p = L.val)
    (hμ : Spec.Kopis.μ p = MU.val) (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hbuf : L.val * 320 + 32 ≤ 1312) (hfit : L.val * 10 * 256 ≤ Usize.max)
    (hL : L.val < 256) (hL0 : 0 < L.val)
    (hout : out_buf.val.length = L.val * 320 + 32) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed L MU seed
        pke.PkePublicKey.serialize ksk.kem_pk.pke_pk out_buf)
      ⦃ (r : Slice U8) =>
          r.val.map (·.bv)
            = (Spec.Kopis.ExpandSecretKey p (arrayToBytes seed)).2.2.1.toList ⦄ := by
  apply WP.spec_bind (expand_from_seed_spec L MU seed p hℓ hμ hMU hbuf hfit hL hL0)
  rintro ksk ⟨_, _, hpkb, _, _, _⟩
  apply WP.spec_mono (pke_serialize_spec ksk.kem_pk.pke_pk out_buf hout hfit)
  rintro r ⟨_, hbytes⟩
  have hmat : (arrayToBytes ksk.kem_pk.pke_pk.matrix_seed).toList
      = (matSeedBytes ksk.kem_pk.pke_pk).toList := by
    simp only [matSeedBytes, Vector.toList_cast]; rfl
  rw [hbytes, hmat, ← pkStructBytes_toList _ p hℓ, hpkb]
  rfl

/-- **Kopis-512: key generation then public-key serialization matches the spec's `pk`.** -/
theorem kopis512_keygen_serialize_spec (seed : Array U8 32#usize) (out_buf : Slice U8)
    (hout : out_buf.val.length = 672) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 2#usize 10#usize seed
        pke.PkePublicKey.serialize ksk.kem_pk.pke_pk out_buf)
      ⦃ (r : Slice U8) =>
          r.val.map (·.bv)
            = (Spec.Kopis.ExpandSecretKey .Kopis_512 (arrayToBytes seed)).2.2.1.toList ⦄ :=
  keygen_serialize_aux seed out_buf rfl rfl (by decide) (by decide) (by scalar_tac)
    (by decide) (by decide) (by rw [hout]; rfl)

/-- **Kopis-768: key generation then public-key serialization matches the spec's `pk`.** -/
theorem kopis768_keygen_serialize_spec (seed : Array U8 32#usize) (out_buf : Slice U8)
    (hout : out_buf.val.length = 992) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 3#usize 8#usize seed
        pke.PkePublicKey.serialize ksk.kem_pk.pke_pk out_buf)
      ⦃ (r : Slice U8) =>
          r.val.map (·.bv)
            = (Spec.Kopis.ExpandSecretKey .Kopis_768 (arrayToBytes seed)).2.2.1.toList ⦄ :=
  keygen_serialize_aux seed out_buf rfl rfl (by decide) (by decide) (by scalar_tac)
    (by decide) (by decide) (by rw [hout]; rfl)

/-- **Kopis-1024: key generation then public-key serialization matches the spec's `pk`.** -/
theorem kopis1024_keygen_serialize_spec (seed : Array U8 32#usize) (out_buf : Slice U8)
    (hout : out_buf.val.length = 1312) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 4#usize 6#usize seed
        pke.PkePublicKey.serialize ksk.kem_pk.pke_pk out_buf)
      ⦃ (r : Slice U8) =>
          r.val.map (·.bv)
            = (Spec.Kopis.ExpandSecretKey .Kopis_1024 (arrayToBytes seed)).2.2.1.toList ⦄ :=
  keygen_serialize_aux seed out_buf rfl rfl (by decide) (by decide) (by scalar_tac)
    (by decide) (by decide) (by rw [hout]; rfl)

end Kopis.Properties
