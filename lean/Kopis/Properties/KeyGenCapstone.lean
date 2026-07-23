import Kopis.Properties.KeyGenHyps
import Kopis.Properties.Impls
open Aeneas Aeneas.Std Result RustKopis
open Spec (𝔹)
namespace Kopis.Properties
-- The three `keygen_encap_spec` composites elaborate a single very large (but finite) `whnf`
-- reduction of the spec-level `KemEncap`/`ExpandDecapKey` terms; they need a raised budget.
set_option maxHeartbeats 20000000

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
  let* ⟨ksk, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ← expand_from_seed_spec 2#usize 10#usize seed .Kopis_512
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  exact kopis512_decapsulate_spec ksk ek (skBytes seed) (pkStructBytes ksk.pke_pk .Kopis_512 rfl)
    h1 h2 h3 h4
    (keygen_hpkvec ksk.pke_pk .Kopis_512 rfl (by decide) h9) h8
    (keygen_hpkmat ksk.pke_pk .Kopis_512 rfl (by decide) h6) h7
    (keygen_hpkh ksk.pke_pk ksk.hash_pke_pk .Kopis_512 rfl (skBytes seed) h5 h4)

/-- **Kopis-768: key-gen then decapsulate matches `KemDecap` (fully unconditional).** -/
theorem kopis768_keygen_decap_spec (seed : Array U8 32#usize) (ek : Array U8 1088#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 3#usize 8#usize seed
        impls.kopis768.Kopis768SecretKey.decapsulate ksk ek)
      ⦃ (r : impls.SharedSecret) =>
          arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_768 (skBytes seed) ((arrayToBytes ek).cast rfl) ⦄ := by
  let* ⟨ksk, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ← expand_from_seed_spec 3#usize 8#usize seed .Kopis_768
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  exact kopis768_decapsulate_spec ksk ek (skBytes seed) (pkStructBytes ksk.pke_pk .Kopis_768 rfl)
    h1 h2 h3 h4
    (keygen_hpkvec ksk.pke_pk .Kopis_768 rfl (by decide) h9) h8
    (keygen_hpkmat ksk.pke_pk .Kopis_768 rfl (by decide) h6) h7
    (keygen_hpkh ksk.pke_pk ksk.hash_pke_pk .Kopis_768 rfl (skBytes seed) h5 h4)

/-- **Kopis-1024: key-gen then decapsulate matches `KemDecap` (fully unconditional).** -/
theorem kopis1024_keygen_decap_spec (seed : Array U8 32#usize) (ek : Array U8 1472#usize) :
    (do let ksk ← kem.KemSecretKey.expand_from_seed 4#usize 6#usize seed
        impls.kopis1024.Kopis1024SecretKey.decapsulate ksk ek)
      ⦃ (r : impls.SharedSecret) =>
          arrayToBytes r
            = Spec.Kopis.KemDecap .Kopis_1024 (skBytes seed) ((arrayToBytes ek).cast rfl) ⦄ := by
  let* ⟨ksk, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ← expand_from_seed_spec 4#usize 6#usize seed .Kopis_1024
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  exact kopis1024_decapsulate_spec ksk ek (skBytes seed) (pkStructBytes ksk.pke_pk .Kopis_1024 rfl)
    h1 h2 h3 h4
    (keygen_hpkvec ksk.pke_pk .Kopis_1024 rfl (by decide) h9) h8
    (keygen_hpkmat ksk.pke_pk .Kopis_1024 rfl (by decide) h6) h7
    (keygen_hpkh ksk.pke_pk ksk.hash_pke_pk .Kopis_1024 rfl (skBytes seed) h5 h4)


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

theorem public_key_spec {L : Usize} (self : kem.KemSecretKey L) :
    kem.KemSecretKey.public_key self
      ⦃ (kpk : kem.KemPublicKey L) =>
          kpk.pke_pk = self.pke_pk ∧ kpk.hash_pke_pk = self.hash_pke_pk ⦄ := by
  unfold kem.KemSecretKey.public_key
  let* ⟨ppk, hppk⟩ ← pke_pk_clone_spec self.pke_pk
  first
    | exact ⟨hppk, rfl⟩
    | exact hppk

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
  let* ⟨ksk, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ← expand_from_seed_spec 2#usize 10#usize seed .Kopis_512
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  let* ⟨kpk, hkvec, hkhash⟩ ← kopis512_public_key_spec ksk
  have hpk3 : pkStructBytes kpk.pke_pk .Kopis_512 rfl
      = Spec.Kopis.SkToPk .Kopis_512 (skBytes seed) := by
    rw [hkvec]; exact h3
  -- pass `SkToPk` as `pk_bytes` so the spec's conclusion is the goal verbatim (as on the
  -- decap side); transport the key-gen public-key facts along `hpk3`.
  exact kopis512_encapsulate_deterministic_spec kpk randomness
    (Spec.Kopis.SkToPk .Kopis_512 (skBytes seed))
    (hpk3 ▸ keygen_hpkvec kpk.pke_pk .Kopis_512 rfl (by decide) (by rw [hkvec]; exact h9))
    (by rw [hkvec]; exact h8)
    (hpk3 ▸ keygen_hpkmat kpk.pke_pk .Kopis_512 rfl (by decide) (by rw [hkvec]; exact h6))
    (by rw [hkvec]; exact h7)
    (hpk3 ▸ keygen_hpkh kpk.pke_pk kpk.hash_pke_pk .Kopis_512 rfl (skBytes seed)
      (by rw [hkhash]; exact h4) (by rw [hkvec]; exact h3))

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
  let* ⟨ksk, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ← expand_from_seed_spec 3#usize 8#usize seed .Kopis_768
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  let* ⟨kpk, hkvec, hkhash⟩ ← kopis768_public_key_spec ksk
  have hpk3 : pkStructBytes kpk.pke_pk .Kopis_768 rfl
      = Spec.Kopis.SkToPk .Kopis_768 (skBytes seed) := by
    rw [hkvec]; exact h3
  exact kopis768_encapsulate_deterministic_spec kpk randomness
    (Spec.Kopis.SkToPk .Kopis_768 (skBytes seed))
    (hpk3 ▸ keygen_hpkvec kpk.pke_pk .Kopis_768 rfl (by decide) (by rw [hkvec]; exact h9))
    (by rw [hkvec]; exact h8)
    (hpk3 ▸ keygen_hpkmat kpk.pke_pk .Kopis_768 rfl (by decide) (by rw [hkvec]; exact h6))
    (by rw [hkvec]; exact h7)
    (hpk3 ▸ keygen_hpkh kpk.pke_pk kpk.hash_pke_pk .Kopis_768 rfl (skBytes seed)
      (by rw [hkhash]; exact h4) (by rw [hkvec]; exact h3))

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
  let* ⟨ksk, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ← expand_from_seed_spec 4#usize 6#usize seed .Kopis_1024
    rfl rfl (by decide) (by decide) (by scalar_tac) (by decide)
  let* ⟨kpk, hkvec, hkhash⟩ ← kopis1024_public_key_spec ksk
  have hpk3 : pkStructBytes kpk.pke_pk .Kopis_1024 rfl
      = Spec.Kopis.SkToPk .Kopis_1024 (skBytes seed) := by
    rw [hkvec]; exact h3
  exact kopis1024_encapsulate_deterministic_spec kpk randomness
    (Spec.Kopis.SkToPk .Kopis_1024 (skBytes seed))
    (hpk3 ▸ keygen_hpkvec kpk.pke_pk .Kopis_1024 rfl (by decide) (by rw [hkvec]; exact h9))
    (by rw [hkvec]; exact h8)
    (hpk3 ▸ keygen_hpkmat kpk.pke_pk .Kopis_1024 rfl (by decide) (by rw [hkvec]; exact h6))
    (by rw [hkvec]; exact h7)
    (hpk3 ▸ keygen_hpkh kpk.pke_pk kpk.hash_pke_pk .Kopis_1024 rfl (skBytes seed)
      (by rw [hkhash]; exact h4) (by rw [hkvec]; exact h3))

end Kopis.Properties
