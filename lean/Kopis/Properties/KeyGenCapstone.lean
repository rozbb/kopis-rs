import Kopis.Properties.KeyGenHyps
import Kopis.Properties.Impls
open Aeneas Aeneas.Std Result RustKopis
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
        impls.kopis512.Kopis512SecretKey.decapsulate ksk ek)
      ⦃ (r : impls.SharedSecret) =>
          arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_512 (skBytes seed) ((arrayToBytes ek).cast rfl) ⦄ := by
  let* ⟨ksk, h1, h2, h3, h4, h5⟩ ← expand_from_seed_spec 2#usize 10#usize seed .Kopis_512
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  exact kopis512_decapsulate_spec ksk ek (skBytes seed) (pkStructBytes ksk.pke_pk .Kopis_512 rfl)
    h1 h2 h3
    (keygen_hpkvec ksk.pke_pk .Kopis_512 rfl (by decide))
    (keygen_hpkmat ksk.pke_pk .Kopis_512 rfl (by decide) h5)
    (keygen_hpkh ksk.pke_pk ksk.hash_pke_pk .Kopis_512 rfl (skBytes seed) h4 h3)

/-- **Kopis-768: key-gen then decapsulate matches `KemDecap` (fully unconditional).** -/
theorem kopis768_keygen_decap_spec (seed : Array U8 32#usize) (ek : Array U8 1088#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 3#usize 8#usize seed
        impls.kopis768.Kopis768SecretKey.decapsulate ksk ek)
      ⦃ (r : impls.SharedSecret) =>
          arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_768 (skBytes seed) ((arrayToBytes ek).cast rfl) ⦄ := by
  let* ⟨ksk, h1, h2, h3, h4, h5⟩ ← expand_from_seed_spec 3#usize 8#usize seed .Kopis_768
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  exact kopis768_decapsulate_spec ksk ek (skBytes seed) (pkStructBytes ksk.pke_pk .Kopis_768 rfl)
    h1 h2 h3
    (keygen_hpkvec ksk.pke_pk .Kopis_768 rfl (by decide))
    (keygen_hpkmat ksk.pke_pk .Kopis_768 rfl (by decide) h5)
    (keygen_hpkh ksk.pke_pk ksk.hash_pke_pk .Kopis_768 rfl (skBytes seed) h4 h3)

/-- **Kopis-1024: key-gen then decapsulate matches `KemDecap` (fully unconditional).** -/
theorem kopis1024_keygen_decap_spec (seed : Array U8 32#usize) (ek : Array U8 1472#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 4#usize 6#usize seed
        impls.kopis1024.Kopis1024SecretKey.decapsulate ksk ek)
      ⦃ (r : impls.SharedSecret) =>
          arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_1024 (skBytes seed) ((arrayToBytes ek).cast rfl) ⦄ := by
  let* ⟨ksk, h1, h2, h3, h4, h5⟩ ← expand_from_seed_spec 4#usize 6#usize seed .Kopis_1024
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  exact kopis1024_decapsulate_spec ksk ek (skBytes seed) (pkStructBytes ksk.pke_pk .Kopis_1024 rfl)
    h1 h2 h3
    (keygen_hpkvec ksk.pke_pk .Kopis_1024 rfl (by decide))
    (keygen_hpkmat ksk.pke_pk .Kopis_1024 rfl (by decide) h5)
    (keygen_hpkh ksk.pke_pk ksk.hash_pke_pk .Kopis_1024 rfl (skBytes seed) h4 h3)


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

theorem pke_pk_clone_spec {L : Usize} (self : pke.PkePublicKey L) :
    pke.PkePublicKey.Insts.CoreCloneClone.clone self
      ⦃ (r : pke.PkePublicKey L) => r = self ⦄ := by
  unfold pke.PkePublicKey.Insts.CoreCloneClone.clone
  let* ⟨a, ha⟩ ← core.array.CloneArray.clone_spec core.clone.CloneU8 self.matrix_seed (by intro x _; rfl)
  let* ⟨m, hm⟩ ← matrix_clone_spec self.vec
  let* ⟨m1, hm1⟩ ← matrix_clone_spec self.mat_a
  subst ha hm hm1
  rfl

theorem public_key_spec {L : Usize} (self : kem.KemSecretKey L) :
    kem.KemSecretKey.public_key self
      ⦃ (kpk : kem.KemPublicKey L) =>
          kpk.pke_pk = self.pke_pk ∧ kpk.hash_pke_pk = self.hash_pke_pk ⦄ := by
  unfold kem.KemSecretKey.public_key
  let* ⟨ppk, hppk⟩ ← pke_pk_clone_spec self.pke_pk
  first
    | exact ⟨hppk, rfl⟩
    | exact hppk
    | (refine ⟨?_, ?_⟩ <;> first | exact hppk | rfl)

/-- Kopis-512 `public_key` (the impls wrapper) copies `pke_pk`/`hash_pke_pk`. -/
theorem kopis512_public_key_spec (self : impls.kopis512.Kopis512SecretKey) :
    impls.kopis512.Kopis512SecretKey.public_key self
      ⦃ (kpk : impls.kopis512.Kopis512PublicKey) =>
          kpk.pke_pk = self.pke_pk ∧ kpk.hash_pke_pk = self.hash_pke_pk ⦄ := by
  unfold impls.kopis512.Kopis512SecretKey.public_key
  let* ⟨kpk, hv, hh⟩ ← public_key_spec self
  exact ⟨hv, hh⟩

/-- **Kopis-512: key-gen → derive public key → encapsulate matches `KemEncap` (unconditional).** -/
theorem kopis512_keygen_encap_spec (seed randomness : Array U8 32#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 2#usize 10#usize seed
        let kpk ← impls.kopis512.Kopis512SecretKey.public_key ksk
        impls.kopis512.Kopis512PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (r : Array U8 736#usize × impls.SharedSecret) =>
          arrayToBytes r.1 = (Spec.Kopis.KemEncap .Kopis_512 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_512 (skBytes seed))).2
          ∧ arrayToBytes r.2 = (Spec.Kopis.KemEncap .Kopis_512 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_512 (skBytes seed))).1 ⦄ := by
  let* ⟨ksk, h1, h2, h3, h4, h5⟩ ← expand_from_seed_spec 2#usize 10#usize seed .Kopis_512
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  let* ⟨kpk, hkvec, hkhash⟩ ← kopis512_public_key_spec ksk
  have hpk3 : pkStructBytes kpk.pke_pk .Kopis_512 rfl
      = Spec.Kopis.SkToPk .Kopis_512 (skBytes seed) := by
    rw [hkvec]; exact h3
  let* ⟨r, hc, hk⟩ ← kopis512_encapsulate_deterministic_spec kpk randomness
    (pkStructBytes kpk.pke_pk .Kopis_512 rfl)
    (keygen_hpkvec kpk.pke_pk .Kopis_512 rfl (by decide))
    (keygen_hpkmat kpk.pke_pk .Kopis_512 rfl (by decide) (by rw [hkvec]; exact h5))
    (keygen_hpkh kpk.pke_pk kpk.hash_pke_pk .Kopis_512 rfl (skBytes seed) (by rw [hkhash]; exact h4)
      (by rw [hkvec]; exact h3))
  rw [hpk3] at hc hk
  exact ⟨hc, hk⟩

/-- Kopis-768 `public_key` (the impls wrapper) copies `pke_pk`/`hash_pke_pk`. -/
theorem kopis768_public_key_spec (self : impls.kopis768.Kopis768SecretKey) :
    impls.kopis768.Kopis768SecretKey.public_key self
      ⦃ (kpk : impls.kopis768.Kopis768PublicKey) =>
          kpk.pke_pk = self.pke_pk ∧ kpk.hash_pke_pk = self.hash_pke_pk ⦄ := by
  unfold impls.kopis768.Kopis768SecretKey.public_key
  let* ⟨kpk, hv, hh⟩ ← public_key_spec self
  exact ⟨hv, hh⟩

/-- **Kopis-768: key-gen → derive public key → encapsulate matches `KemEncap` (unconditional).** -/
theorem kopis768_keygen_encap_spec (seed randomness : Array U8 32#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 3#usize 8#usize seed
        let kpk ← impls.kopis768.Kopis768SecretKey.public_key ksk
        impls.kopis768.Kopis768PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (r : Array U8 1088#usize × impls.SharedSecret) =>
          arrayToBytes r.1 = (Spec.Kopis.KemEncap .Kopis_768 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_768 (skBytes seed))).2
          ∧ arrayToBytes r.2 = (Spec.Kopis.KemEncap .Kopis_768 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_768 (skBytes seed))).1 ⦄ := by
  let* ⟨ksk, h1, h2, h3, h4, h5⟩ ← expand_from_seed_spec 3#usize 8#usize seed .Kopis_768
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  let* ⟨kpk, hkvec, hkhash⟩ ← kopis768_public_key_spec ksk
  have hpk3 : pkStructBytes kpk.pke_pk .Kopis_768 rfl
      = Spec.Kopis.SkToPk .Kopis_768 (skBytes seed) := by
    rw [hkvec]; exact h3
  let* ⟨r, hc, hk⟩ ← kopis768_encapsulate_deterministic_spec kpk randomness
    (pkStructBytes kpk.pke_pk .Kopis_768 rfl)
    (keygen_hpkvec kpk.pke_pk .Kopis_768 rfl (by decide))
    (keygen_hpkmat kpk.pke_pk .Kopis_768 rfl (by decide) (by rw [hkvec]; exact h5))
    (keygen_hpkh kpk.pke_pk kpk.hash_pke_pk .Kopis_768 rfl (skBytes seed) (by rw [hkhash]; exact h4)
      (by rw [hkvec]; exact h3))
  rw [hpk3] at hc hk
  exact ⟨hc, hk⟩

/-- Kopis-1024 `public_key` (the impls wrapper) copies `pke_pk`/`hash_pke_pk`. -/
theorem kopis1024_public_key_spec (self : impls.kopis1024.Kopis1024SecretKey) :
    impls.kopis1024.Kopis1024SecretKey.public_key self
      ⦃ (kpk : impls.kopis1024.Kopis1024PublicKey) =>
          kpk.pke_pk = self.pke_pk ∧ kpk.hash_pke_pk = self.hash_pke_pk ⦄ := by
  unfold impls.kopis1024.Kopis1024SecretKey.public_key
  let* ⟨kpk, hv, hh⟩ ← public_key_spec self
  exact ⟨hv, hh⟩

/-- **Kopis-1024: key-gen → derive public key → encapsulate matches `KemEncap` (unconditional).** -/
theorem kopis1024_keygen_encap_spec (seed randomness : Array U8 32#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 4#usize 6#usize seed
        let kpk ← impls.kopis1024.Kopis1024SecretKey.public_key ksk
        impls.kopis1024.Kopis1024PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (r : Array U8 1472#usize × impls.SharedSecret) =>
          arrayToBytes r.1 = (Spec.Kopis.KemEncap .Kopis_1024 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_1024 (skBytes seed))).2
          ∧ arrayToBytes r.2 = (Spec.Kopis.KemEncap .Kopis_1024 ((arrayToBytes randomness).cast rfl)
              (Spec.Kopis.SkToPk .Kopis_1024 (skBytes seed))).1 ⦄ := by
  let* ⟨ksk, h1, h2, h3, h4, h5⟩ ← expand_from_seed_spec 4#usize 6#usize seed .Kopis_1024
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  let* ⟨kpk, hkvec, hkhash⟩ ← kopis1024_public_key_spec ksk
  have hpk3 : pkStructBytes kpk.pke_pk .Kopis_1024 rfl
      = Spec.Kopis.SkToPk .Kopis_1024 (skBytes seed) := by
    rw [hkvec]; exact h3
  let* ⟨r, hc, hk⟩ ← kopis1024_encapsulate_deterministic_spec kpk randomness
    (pkStructBytes kpk.pke_pk .Kopis_1024 rfl)
    (keygen_hpkvec kpk.pke_pk .Kopis_1024 rfl (by decide))
    (keygen_hpkmat kpk.pke_pk .Kopis_1024 rfl (by decide) (by rw [hkvec]; exact h5))
    (keygen_hpkh kpk.pke_pk kpk.hash_pke_pk .Kopis_1024 rfl (skBytes seed) (by rw [hkhash]; exact h4)
      (by rw [hkvec]; exact h3))
  rw [hpk3] at hc hk
  exact ⟨hc, hk⟩

end Kopis.Properties
