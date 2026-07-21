import Kopis.Properties.ExpandDecap
open Aeneas Aeneas.Std Result kopis
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
    (hL : L.val < 256) :
    kem.KemSecretKey.expand_from_seed L MU seed
      ⦃ (ksk : kem.KemSecretKey L) =>
          toVector13 ksk.pke_sk = hℓ ▸ (Spec.Kopis.ExpandDecapKey p (skBytes seed)).1 ∧
          arrayToBytes ksk.z = (Spec.Kopis.ExpandDecapKey p (skBytes seed)).2.1 ∧
          pkStructBytes ksk.pke_pk p hℓ = (Spec.Kopis.ExpandDecapKey p (skBytes seed)).2.2.1 ∧
          arrayToBytes ksk.hash_pke_pk = (Spec.Kopis.ExpandDecapKey p (skBytes seed)).2.2.2 ∧
          toMatrix13 ksk.pke_pk.mat_a
            = Spec.Kopis.GenMat L.val (arrayToBytes ksk.pke_pk.matrix_seed) ⦄ := by
  unfold kem.KemSecretKey.expand_from_seed
  let* ⟨pke_sk, z, pke_pk, hash_pke_pk, h1, h2, h3, h4, h5⟩ ←
    expand_decap_key_spec L MU seed p hℓ hμ hMU hbuf hfit hL
  exact ⟨h1, h2, h3, h4, h5⟩

end Kopis.Properties
