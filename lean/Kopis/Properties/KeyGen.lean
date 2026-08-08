import Kopis.Properties.ExpandDecap
open Aeneas Aeneas.Std Result RustKopisSerial
open Spec (𝔹)
namespace Kopis.Properties
set_option maxHeartbeats 1000000

/-- **Rust KEM key expansion matches the spec `ExpandDecapKey`.**  `expand_from_seed`
runs `expand_decap_key` and packs the four outputs into a `KemSecretKey`; each field is
exactly the corresponding `ExpandDecapKey` component (the secret vector, the reject seed
`z`, the serialized public key, and its hash). -/
theorem expand_from_seed_spec (L MU : Usize) (seed : Array U8 32#usize)
    (p : Spec.Kopis.ParameterSet)
    (hℓ : Spec.Kopis.ℓ p = L.val) (hμ : Spec.Kopis.μ p = MU.val)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hbuf : L.val * 320 + 32 ≤ 1312) (hfit : L.val * 10 * 256 ≤ Usize.max)
    (hL : L.val < 256) (_hL0 : 0 < L.val) :
    kem.KemSecretKey.expand_from_seed L MU seed
      ⦃ (ksk : kem.KemSecretKey L) =>
          (∃ S : Mat L 1#usize, ksk.pke_sk = nttFwdS S ∧
              toVector13 S = hℓ ▸ (Spec.Kopis.ExpandDecapKey p (skBytes seed)).1 ∧
              SecretBounded S ((MU.val / 2 : ℕ) : ℤ)) ∧
          arrayToBytes ksk.z = (Spec.Kopis.ExpandDecapKey p (skBytes seed)).2.1 ∧
          pkStructBytes ksk.pke_pk p hℓ = (Spec.Kopis.ExpandDecapKey p (skBytes seed)).2.2.1 ∧
          arrayToBytes ksk.hash_pke_pk = (Spec.Kopis.ExpandDecapKey p (skBytes seed)).2.2.2 ∧
          (∃ Amat : Mat L L, ksk.pke_pk.mat_a_ntt = nttFwdU Amat ∧
              toMatrix13 Amat = Spec.Kopis.GenMat L.val (arrayToBytes ksk.pke_pk.matrix_seed) ∧
              UniformBounded Amat) ∧
          (∃ V : Mat L 1#usize, ksk.pke_pk.vec_ntt = nttFwdU V ∧
              UniformBounded V ∧
              vecBytesFlat ksk.pke_pk = Spec.Kopis.PolyVector.serialize 10 (toVecN 10 V)) ⦄ := by
  unfold kem.KemSecretKey.expand_from_seed
  -- `let*` splits each bundled existential into its witness followed by its conjuncts, so the
  -- pattern names 4 tuple components + 15 postcondition parts; regroup them to rebuild the
  -- three existentials.
  let* ⟨pke_sk, z, pke_pk, hash_pke_pk,
        S, hS1, hS2, hS3, hz, hpk, hhash,
        Am, hA1, hA2, hA3, V, hV1, hV2, hV3⟩ ←
    expand_decap_key_spec L MU seed p hℓ hμ hMU hbuf hfit hL
  exact ⟨⟨S, hS1, hS2, hS3⟩, hz, hpk, hhash, ⟨Am, hA1, hA2, hA3⟩, ⟨V, hV1, hV2, hV3⟩⟩

end Kopis.Properties
