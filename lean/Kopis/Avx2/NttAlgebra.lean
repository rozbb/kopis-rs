/-
  # Kopis/Avx2/NttAlgebra.lean — the transform algebra, over any modulus (plan phase F4).

  `Kopis/Properties/NttMath.lean` develops the Cooley-Tukey / Gentleman-Sande algebra for the
  portable backend's single prime `p = 50330113`, and it is specialised to it throughout: `Zp`,
  `zetaP`, `cst` and the `decide`d table checks all name `p`.  The AVX2 backend runs the *same*
  network twice, over `q₁ = 7681` and `q₂ = 10753`, so phase F4 needs that algebra at two other
  moduli.

  This file is that algebra with the modulus abstracted away: a commutative ring `K` and a
  twiddle function `ζ : ℕ → K` satisfying one hypothesis, `ζ k ² = cst k`, where `cst` is the
  CRT-tree node constant built from `ζ` exactly as the serial file builds it.  Everything the
  transform's correctness rests on follows from that alone — the specific prime never appears.

  What is *not* here is anything about the code: `State_ct` says what one Cooley-Tukey layer does
  to the invariant, and it is the caller's job to show the layer's butterflies have that shape.
-/
import Mathlib.Tactic

namespace Kopis.Avx2.NttAlg

variable {K : Type*} [CommRing K]

/-! ## The CRT tree

Node `k` of the tree carries the modulus `X^m − cst k`.  The root is `cst 1 = −1`, i.e. the ring
`X²⁵⁶ + 1`; a node's two children carry `±` the twiddle that split it. -/

/-- The CRT-tree node constant built from a twiddle table. -/
def cst (ζ : ℕ → K) (k : ℕ) : K :=
  if k = 1 then -1 else if k % 2 = 0 then ζ (k / 2) else -(ζ (k / 2))

theorem cst_one (ζ : ℕ → K) : cst ζ 1 = -1 := rfl

theorem cst_even (ζ : ℕ → K) {k : ℕ} (_hk : 1 ≤ k) : cst ζ (2 * k) = ζ k := by
  unfold cst
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem cst_odd (ζ : ℕ → K) {k : ℕ} (hk : 1 ≤ k) : cst ζ (2 * k + 1) = -(ζ k) := by
  unfold cst
  rw [if_neg (by omega), if_neg (by omega)]
  congr 2
  omega

/-- Splitting a range of even length into its even and odd halves. -/
theorem sum_range_two (n : ℕ) (g : ℕ → K) :
    ∑ q ∈ Finset.range (2 * n), g q
      = (∑ q ∈ Finset.range n, g (2 * q)) + ∑ q ∈ Finset.range n, g (2 * q + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-! ## The transform invariant -/

/-- **The transform invariant.**  `State ζ nb m c f a` says the array `a` holds, scaled by `c`,
the CRT image of `f` at the tree level with `nb` blocks of size `m`: block `b` sits at offset
`b·m` and holds the coefficients of `f mod (X^m − cst (nb + b))`.

`State ζ 1 256 1 f a` says `a = f`; `State ζ 256 1 1 f a` says `a b` is the evaluation of `f` at
the `b`-th leaf constant. -/
def State (ζ : ℕ → K) (nb m : ℕ) (c : K) (f a : ℕ → K) : Prop :=
  ∀ b < nb, ∀ r < m,
    a (b * m + r) = c * ∑ q ∈ Finset.range nb, f (q * m + r) * cst ζ (nb + b) ^ q

theorem State_root {ζ : ℕ → K} {c : K} {f a : ℕ → K} (h : State ζ 1 256 c f a)
    (r : ℕ) (hr : r < 256) : a r = c * f r := by
  have := h 0 (by norm_num) r hr
  simpa using this

theorem State_root_intro {ζ : ℕ → K} {c : K} {f a : ℕ → K} (h : ∀ r < 256, a r = c * f r) :
    State ζ 1 256 c f a := by
  intro b hb r hr
  have hb0 : b = 0 := by omega
  subst hb0
  simpa using h r hr

theorem State_leaf {ζ : ℕ → K} {c : K} {f a : ℕ → K} (h : State ζ 256 1 c f a)
    (b : ℕ) (hb : b < 256) :
    a b = c * ∑ i ∈ Finset.range 256, f i * cst ζ (256 + b) ^ i := by
  have := h b hb 0 (by norm_num)
  simpa using this

/-- **One Cooley-Tukey layer.**  Splitting each block of size `2m'` in two with the twiddle
`ζ (nb + b)` refines the CRT factorisation by one level.  The only thing asked of the table is
that each twiddle squares to its parent's node constant. -/
theorem State_ct {ζ : ℕ → K} (hsq : ∀ k, 1 ≤ k → k < 256 → ζ k ^ 2 = cst ζ k)
    {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    {c : K} {f a a' : ℕ → K}
    (hst : State ζ nb (2 * m') c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r)
          = a (b * (2 * m') + r) + ζ (nb + b) * a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
          = a (b * (2 * m') + r) - ζ (nb + b) * a (b * (2 * m') + m' + r)) :
    State ζ (2 * nb) m' c f a' := by
  intro b' hb' r hr
  obtain ⟨b, hb, hhalf⟩ : ∃ b, b < nb ∧ (b' = 2 * b ∨ b' = 2 * b + 1) :=
    ⟨b' / 2, by omega, by omega⟩
  have hk1 : 1 ≤ nb + b := by omega
  have hk256 : nb + b < 256 := by omega
  have hγ2 : ζ (nb + b) ^ 2 = cst ζ (nb + b) := hsq _ hk1 hk256
  have hlo := hst b hb r (by omega)
  have hhi := hst b hb (m' + r) (by omega)
  have hidx : b * (2 * m') + (m' + r) = b * (2 * m') + m' + r := by ring
  rw [hidx] at hhi
  -- the even/odd split of a child sum, for either child constant `δ` with `δ² = cst (nb+b)`
  have key : ∀ δ : K, δ ^ 2 = cst ζ (nb + b) →
      ∑ q ∈ Finset.range (2 * nb), f (q * m' + r) * δ ^ q
        = (∑ q ∈ Finset.range nb, f (q * (2 * m') + r) * cst ζ (nb + b) ^ q)
          + δ * ∑ q ∈ Finset.range nb, f (q * (2 * m') + (m' + r)) * cst ζ (nb + b) ^ q := by
    intro δ hδ
    rw [sum_range_two nb (fun q => f (q * m' + r) * δ ^ q), Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [show 2 * q * m' + r = q * (2 * m') + r by ring, ← hδ, ← pow_mul]
    · refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [show (2 * q + 1) * m' + r = q * (2 * m') + (m' + r) by ring, ← hδ, pow_succ, ← pow_mul]
      ring
  have hnegsq : (-(ζ (nb + b))) ^ 2 = cst ζ (nb + b) := by
    rw [show (-(ζ (nb + b))) ^ 2 = ζ (nb + b) ^ 2 by ring]; exact hγ2
  rcases hhalf with rfl | rfl
  · rw [show 2 * b * m' + r = b * (2 * m') + r by ring, (hbut b hb r hr).1, hlo, hhi,
      show 2 * nb + 2 * b = 2 * (nb + b) by ring, cst_even ζ hk1, key (ζ (nb + b)) hγ2]
    ring
  · rw [show (2 * b + 1) * m' + r = b * (2 * m') + m' + r by ring, (hbut b hb r hr).2, hlo, hhi,
      show 2 * nb + (2 * b + 1) = 2 * (nb + b) + 1 by ring, cst_odd ζ hk1,
      key (-(ζ (nb + b))) hnegsq]
    ring

/-! ## Every leaf constant is a 256th root of −1

Iterating `cst_sq` down the tree: `cst (256+b) ^ 256 = cst 1 = −1`.  That is what makes
evaluation at a leaf a ring homomorphism out of the negacyclic ring. -/

theorem cst_sq {ζ : ℕ → K} (hsq : ∀ k, 1 ≤ k → k < 256 → ζ k ^ 2 = cst ζ k)
    {j : ℕ} (hj : 2 ≤ j) (hj2 : j < 512) : cst ζ j ^ 2 = cst ζ (j / 2) := by
  obtain ⟨k, hk⟩ : ∃ k, j / 2 = k := ⟨j / 2, rfl⟩
  have hk1 : 1 ≤ k := by omega
  have hk256 : k < 256 := by omega
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨t, ht⟩ := he
    have hjk : j = 2 * k := by omega
    subst hjk
    rw [cst_even ζ hk1, hsq k hk1 hk256, hk]
  · obtain ⟨t, ht⟩ := ho
    have hjk : j = 2 * k + 1 := by omega
    subst hjk
    have hneg : (-(ζ k)) ^ 2 = ζ k ^ 2 := by ring
    rw [cst_odd ζ hk1, hneg, hsq k hk1 hk256, hk]

theorem cst_leaf_pow {ζ : ℕ → K} (hsq : ∀ k, 1 ≤ k → k < 256 → ζ k ^ 2 = cst ζ k)
    (b : ℕ) (hb : b < 256) : cst ζ (256 + b) ^ 256 = -1 := by
  have step : ∀ (d j : ℕ), 2 ^ d ≤ j → j < 2 ^ (d + 1) → j < 512 →
      cst ζ j ^ (2 ^ d) = cst ζ 1 := by
    intro d
    induction d with
    | zero =>
      intro j h1 h2 _
      have hj : j = 1 := by
        have e2 : (2 : ℕ) ^ (0 + 1) = 2 := rfl
        have e1 : (2 : ℕ) ^ 0 = 1 := rfl
        omega
      rw [hj, show (2 : ℕ) ^ 0 = 1 from rfl, pow_one]
    | succ d ih =>
      intro j h1 h2 h3
      have hpd : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by norm_num)
      have hsplit : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      have hsplit2 : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
      have hj2 : 2 ≤ j := by omega
      have hdiv1 : 2 ^ d ≤ j / 2 := by omega
      have hdiv2 : j / 2 < 2 ^ (d + 1) := by omega
      have hpow : cst ζ j ^ (2 ^ (d + 1)) = (cst ζ j ^ 2) ^ (2 ^ d) := by
        rw [← pow_mul, ← hsplit]
      rw [hpow, cst_sq hsq hj2 h3]
      exact ih (j / 2) hdiv1 hdiv2 (by omega)
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have e9 : (2 : ℕ) ^ (8 + 1) = 512 := by norm_num
  have h := step 8 (256 + b) (by omega) (by omega) (by omega)
  rw [e8] at h
  rw [h, cst_one]

/-! ## The convolution theorem

Evaluation at any `c` with `c²⁵⁶ = −1` is a ring homomorphism out of the negacyclic ring, so the
pointwise product of two transforms is the transform of the negacyclic product.  Nothing here
depends on the modulus or the table. -/

/-- The negacyclic convolution: `X²⁵⁶ = −1`, so `f i · g j` lands on `(i+j) mod 256` with a sign
flip when `i + j ≥ 256`. -/
def nconv (f g : ℕ → K) (n : ℕ) : K :=
  ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
    if i + j = n then f i * g j else if i + j = n + 256 then -(f i * g j) else 0

theorem Ev_nconv (f g : ℕ → K) {c : K} (hc : c ^ 256 = -1) :
    (∑ i ∈ Finset.range 256, f i * c ^ i) * (∑ j ∈ Finset.range 256, g j * c ^ j)
      = ∑ n ∈ Finset.range 256, nconv f g n * c ^ n := by
  have key : ∀ i j : ℕ, i < 256 → j < 256 →
      (∑ n ∈ Finset.range 256,
        (if i + j = n then f i * g j else if i + j = n + 256 then -(f i * g j) else 0) * c ^ n)
        = f i * g j * c ^ (i + j) := by
    intro i j hi hj
    rcases lt_or_ge (i + j) 256 with hlt | hge
    · rw [Finset.sum_eq_single (i + j)]
      · rw [if_pos rfl]
      · intro n _ hne
        rw [if_neg (fun h => hne h.symm), if_neg (by omega), zero_mul]
      · intro hmem; exact absurd (Finset.mem_range.mpr hlt) hmem
    · have hsub : i + j - 256 < 256 := by omega
      have he : i + j = (i + j - 256) + 256 := by omega
      have hpow : c ^ (i + j) = -(c ^ (i + j - 256)) := by
        conv_lhs => rw [he]
        rw [pow_add, hc]
        ring
      rw [Finset.sum_eq_single (i + j - 256)]
      · rw [if_neg (by omega), if_pos (by omega), hpow]
        ring
      · intro n hn hne
        have hn' : n < 256 := Finset.mem_range.mp hn
        rw [if_neg (by omega), if_neg (by omega), zero_mul]
      · intro hmem; exact absurd (Finset.mem_range.mpr hsub) hmem
  calc (∑ i ∈ Finset.range 256, f i * c ^ i) * (∑ j ∈ Finset.range 256, g j * c ^ j)
      = ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256, f i * g j * c ^ (i + j) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [pow_add]; ring
    _ = ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256, ∑ n ∈ Finset.range 256,
          (if i + j = n then f i * g j else if i + j = n + 256 then -(f i * g j) else 0)
            * c ^ n := by
        refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
        rw [key i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
    _ = ∑ i ∈ Finset.range 256, ∑ n ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
          (if i + j = n then f i * g j else if i + j = n + 256 then -(f i * g j) else 0)
            * c ^ n :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ n ∈ Finset.range 256, ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
          (if i + j = n then f i * g j else if i + j = n + 256 then -(f i * g j) else 0)
            * c ^ n := Finset.sum_comm
    _ = ∑ n ∈ Finset.range 256, nconv f g n * c ^ n := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        unfold nconv
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])

/-- **Pointwise multiplication in the transform domain is negacyclic convolution.**  If `a` and
`b` are the leaf states of `f` and `g`, their pointwise product is the leaf state of `f ∗ g`.
This is the statement phase F4 needs at each of the two primes: whatever the vector code does
between the endpoints, if it reaches the leaf state then multiplying lanewise multiplies the
polynomials. -/
theorem State_leaf_mul {ζ : ℕ → K} (hsq : ∀ k, 1 ≤ k → k < 256 → ζ k ^ 2 = cst ζ k)
    {f g a b : ℕ → K} (ha : State ζ 256 1 1 f a) (hb : State ζ 256 1 1 g b) :
    State ζ 256 1 1 (nconv f g) (fun n => a n * b n) := by
  intro n hn r hr
  have hr0 : r = 0 := by omega
  subst hr0
  have hna : a (n * 1 + 0) = ∑ i ∈ Finset.range 256, f i * cst ζ (256 + n) ^ i := by
    have := State_leaf ha n hn
    simpa using this
  have hnb : b (n * 1 + 0) = ∑ j ∈ Finset.range 256, g j * cst ζ (256 + n) ^ j := by
    have := State_leaf hb n hn
    simpa using this
  simp only [hna, hnb, one_mul]
  rw [Ev_nconv f g (cst_leaf_pow hsq n hn)]
  exact Finset.sum_congr rfl (fun q _ => by rw [show q * 1 + 0 = q from by ring])

/-- **One Gentleman-Sande layer.**  Merging block pairs performs the inverse CRT reconstruction,
up to the factor `2` each layer leaves behind.  The `-ζ (2·nb−1−b)` the inverse loop forms is the
inverse of the twiddle the forward layer used, which is what `hpair` records. -/
theorem State_gs {ζ : ℕ → K} (hsq : ∀ k, 1 ≤ k → k < 256 → ζ k ^ 2 = cst ζ k)
    (hpair : ∀ nb b : ℕ, (∃ j, j < 8 ∧ nb = 2 ^ j) → b < nb →
      ζ (nb + b) * ζ (2 * nb - 1 - b) = -1)
    {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256) (hpow : ∃ j, j < 8 ∧ nb = 2 ^ j)
    {c : K} {f a a' : ℕ → K}
    (hst : State ζ (2 * nb) m' c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r) = a (b * (2 * m') + r) + a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
          = (-(ζ (2 * nb - 1 - b))) * (a (b * (2 * m') + r) - a (b * (2 * m') + m' + r))) :
    State ζ nb (2 * m') (2 * c) f a' := by
  intro b hb s hs
  have hk1 : 1 ≤ nb + b := by omega
  have hk256 : nb + b < 256 := by omega
  have hγ2 : ζ (nb + b) ^ 2 = cst ζ (nb + b) := hsq _ hk1 hk256
  have hδ : -(ζ (2 * nb - 1 - b)) * ζ (nb + b) = 1 := by
    have h := hpair nb b hpow hb
    rw [neg_mul, mul_comm, h, neg_neg]
  have hclo : ∀ t < m', a (b * (2 * m') + t)
      = c * ∑ q ∈ Finset.range (2 * nb), f (q * m' + t) * ζ (nb + b) ^ q := by
    intro t ht
    have h := hst (2 * b) (by omega) t ht
    rwa [show 2 * b * m' + t = b * (2 * m') + t by ring,
      show 2 * nb + 2 * b = 2 * (nb + b) by ring, cst_even ζ hk1] at h
  have hchi : ∀ t < m', a (b * (2 * m') + m' + t)
      = c * ∑ q ∈ Finset.range (2 * nb), f (q * m' + t) * (-(ζ (nb + b))) ^ q := by
    intro t ht
    have h := hst (2 * b + 1) (by omega) t ht
    rwa [show (2 * b + 1) * m' + t = b * (2 * m') + m' + t by ring,
      show 2 * nb + (2 * b + 1) = 2 * (nb + b) + 1 by ring, cst_odd ζ hk1] at h
  have hsplit : ∀ (δ : K) (t : ℕ),
      ∑ q ∈ Finset.range (2 * nb), f (q * m' + t) * δ ^ q
        = (∑ q ∈ Finset.range nb, f (q * (2 * m') + t) * (δ ^ 2) ^ q)
          + δ * ∑ q ∈ Finset.range nb, f (q * (2 * m') + (m' + t)) * (δ ^ 2) ^ q := by
    intro δ t
    rw [sum_range_two nb (fun q => f (q * m' + t) * δ ^ q), Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [show 2 * q * m' + t = q * (2 * m') + t by ring, ← pow_mul]
    · refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [show (2 * q + 1) * m' + t = q * (2 * m') + (m' + t) by ring, pow_succ, ← pow_mul]
      ring
  have hgsq : ((-(ζ (nb + b))) ^ 2) = cst ζ (nb + b) := by
    rw [show (-(ζ (nb + b))) ^ 2 = ζ (nb + b) ^ 2 by ring]; exact hγ2
  rcases lt_or_ge s m' with hslt | hsge
  · have hlo := hclo s hslt
    have hhi := hchi s hslt
    rw [hsplit (ζ (nb + b)) s, hγ2] at hlo
    rw [hsplit (-(ζ (nb + b))) s, hgsq] at hhi
    rw [(hbut b hb s hslt).1, hlo, hhi]
    ring
  · obtain ⟨t, rfl⟩ : ∃ t, s = m' + t := ⟨s - m', by omega⟩
    have ht : t < m' := by omega
    have hlo := hclo t ht
    have hhi := hchi t ht
    rw [hsplit (ζ (nb + b)) t, hγ2] at hlo
    rw [hsplit (-(ζ (nb + b))) t, hgsq] at hhi
    rw [show b * (2 * m') + (m' + t) = b * (2 * m') + m' + t by ring,
      (hbut b hb t ht).2, hlo, hhi]
    have hexp : ∀ A B : K,
        (-(ζ (2 * nb - 1 - b))) * (c * (A + ζ (nb + b) * B) - c * (A + (-(ζ (nb + b))) * B))
          = ((-(ζ (2 * nb - 1 - b))) * ζ (nb + b)) * (2 * c * B) := by
      intro A B; ring
    rw [hexp, hδ, one_mul]

end Kopis.Avx2.NttAlg
