import Kopis.Properties.KeyGenHyps
import Kopis.Properties.Impls
open Aeneas Aeneas.Std Result RustKopisSerial
open Spec (𝔹)
namespace Kopis.Properties
set_option maxHeartbeats 4000000

/-! ## Unconditional decapsulation for a key-gen output.

Composing `expand_from_seed_spec` (key-gen = `ExpandDecapKey`) with the hypothesis
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


@[step]
theorem matrix_clone_spec {X Y : Usize} (self : arithmetic.matrix_arith.Matrix X Y) :
    arithmetic.matrix_arith.Matrix.Insts.CoreCloneClone.clone self
      ⦃ (r : arithmetic.matrix_arith.Matrix X Y) => r = self ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.Insts.CoreCloneClone.clone
  let* ⟨a, ha⟩ ← core.array.CloneArray.clone_spec
    (core.clone.CloneArray Y arithmetic.ring_arith.RingElem.Insts.CoreCloneClone) self (by
    intro x _
    show core.array.CloneArray.clone arithmetic.ring_arith.RingElem.Insts.CoreCloneClone x = ok x
    obtain ⟨x', hx', hxx'⟩ :=
      Aeneas.Std.WP.spec_imp_exists (core.array.CloneArray.clone_spec
        arithmetic.ring_arith.RingElem.Insts.CoreCloneClone x (fun y _ => rfl))
    rw [hx', ← hxx'])
  exact ha.symm

theorem ntt_matrix_clone_spec {X Y : Usize} (self : arithmetic.ntt.NttMatrix X Y) :
    arithmetic.ntt.NttMatrix.Insts.CoreCloneClone.clone self
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) => r = self ⦄ := by
  unfold arithmetic.ntt.NttMatrix.Insts.CoreCloneClone.clone
  let* ⟨a, ha⟩ ← core.array.CloneArray.clone_spec
    (core.clone.CloneArray Y arithmetic.ntt.NttElem.Insts.CoreCloneClone) self (by
    intro x _
    show core.array.CloneArray.clone arithmetic.ntt.NttElem.Insts.CoreCloneClone x = ok x
    obtain ⟨x', hx', hxx'⟩ :=
      Aeneas.Std.WP.spec_imp_exists (core.array.CloneArray.clone_spec
        arithmetic.ntt.NttElem.Insts.CoreCloneClone x (fun y _ => rfl))
    rw [hx', ← hxx'])
  exact ha.symm

theorem pke_pk_clone_spec {L : Usize} (self : pke.PkePublicKey L) :
    pke.PkePublicKey.Insts.CoreCloneClone.clone self
      ⦃ (r : pke.PkePublicKey L) => r = self ⦄ := by
  unfold pke.PkePublicKey.Insts.CoreCloneClone.clone
  let* ⟨a, ha⟩ ← core.array.CloneArray.clone_spec core.clone.CloneU8 self.matrix_seed (by intro x _; rfl)
  let* ⟨nm, hnm⟩ ← ntt_matrix_clone_spec self.mat_a_ntt
  let* ⟨a1, ha1⟩ ← core.array.CloneArray.clone_spec
    (core.clone.CloneArray 320#usize core.clone.CloneU8) self.vec_bytes (by
    intro x _
    show core.array.CloneArray.clone core.clone.CloneU8 x = ok x
    obtain ⟨x', hx', hxx'⟩ :=
      Aeneas.Std.WP.spec_imp_exists (core.array.CloneArray.clone_spec
        core.clone.CloneU8 x (fun y _ => rfl))
    rw [hx', ← hxx'])
  let* ⟨nm1, hnm1⟩ ← ntt_matrix_clone_spec self.vec_ntt
  subst ha hnm ha1 hnm1
  rfl

/-- `SkToPk` unfolds definitionally to the public-key component of `ExpandDecapKey`. Proved
here (cheaply, by `rfl`) *before* the local-irreducible attribute below, so the
`keygen_encap` composites can bridge the two forms by rewriting with this equation rather than
by a `whnf` that would unfold the huge spec term. -/
theorem skToPk_eq (p : Spec.Kopis.ParameterSet) (sk : 𝔹 32) :
    Spec.Kopis.SkToPk p sk = (Spec.Kopis.ExpandDecapKey p sk).2.2.1 := rfl

-- The three `keygen_encap_spec` composites below check the `keygen_hpk*` facts against
-- `encapsulate_deterministic_spec`'s expected types over the huge spec-level `KemEncap` /
-- `ExpandDecapKey` / `SkToPk` terms.  Making those three spec definitions *locally* irreducible
-- stops `whnf`/`kabstract` from unfolding them during elaboration — which is exactly what
-- otherwise blows up — while the proofs only ever touch them through `skToPk_eq` and the
-- already-compiled specs.  (The decapsulation capstones above are unaffected: this attribute
-- takes effect only from here onward in the file.)
attribute [local irreducible]
  Spec.Kopis.SkToPk Spec.Kopis.KemEncap Spec.Kopis.ExpandDecapKey

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

end Kopis.Properties
