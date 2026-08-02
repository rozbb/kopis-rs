/-
  # Kopis/Properties/NttMath.lean — the pure-mathematical layer of the NTT proof.

  This file contains no Hoare triples and reads nothing from the extracted code except the
  `ZETAS` table itself.  It develops, over the auxiliary prime `p = 50330113`, exactly the
  algebra that the Cooley-Tukey / Gentleman-Sande networks of `src/arithmetic/ntt.rs` need, in
  the form the loop proofs consume.

  ## The design: one invariant, two steps, no roots of unity

  The textbook route to NTT correctness goes through a primitive `512`-th root of unity `ψ`,
  bit-reversal permutations, and Vandermonde invertibility.  None of that is needed here, and
  all of it is expensive to formalise.  Instead we track the *CRT tree* directly.

  Write `X²⁵⁶ + 1 = X²⁵⁶ - c₁` with `c₁ = -1`.  Each butterfly layer refines a factorisation
  using the classical split

      ℤ_p[X]/(X^{2m} - γ²)  ≅  ℤ_p[X]/(X^m - γ)  ×  ℤ_p[X]/(X^m + γ),

  so the node constants satisfy `c_{2k} = γ_k`, `c_{2k+1} = -γ_k` with `γ_k² = c_k`, where `γ_k`
  is the plain (non-Montgomery) `k`-th table entry `zetaP k`.  Those relations — and the pairing
  relation the inverse transform needs — are *concrete numeric facts* about the shipped `ZETAS`
  table, discharged here by `decide`.  Nothing about `ψ` or bit reversal is ever used: the table
  is taken as given data, and only its arithmetic relations matter.

  The single invariant `State nb m c f a` says that the array `a` is `c` times the CRT image of
  the polynomial `f` at the tree level with `nb` blocks of size `m`: block `b` sits at offset
  `b·m` and holds the coefficients of `f mod (X^m - c_{nb+b})`.  Then

  * `State_ct` — one Cooley-Tukey layer takes `State nb (2m') c f` to `State (2nb) m' c f`;
  * `State_gs` — one Gentleman-Sande layer takes `State (2nb) m' c f` to `State nb (2m') (2c) f`.

  The forward transform is eight `State_ct` steps from `State 1 256 1 f f` to `State 256 1 1 f`,
  whose meaning (`State_leaf`) is that `a b` is the evaluation of `f` at the leaf constant
  `c_{256+b}`.  The inverse is eight `State_gs` steps back to `State 1 256 256 …`, whose meaning
  (`State_root`) is `a r = 256 · c · f r`.  The factor of two per layer is exactly what
  `INVNTT_SCALE` cancels.

  Finally `Ev_nconv` is the convolution theorem: evaluation at any `c` with `c²⁵⁶ = -1` is a ring
  homomorphism out of the negacyclic ring, which is what makes the pointwise product of
  transforms compute the negacyclic product.  `cst_leaf_pow` supplies `c²⁵⁶ = -1` for every leaf.
-/
import ExtractedRust
import Spec.Kopis.Spec
import Mathlib.Data.ZMod.Basic

open Aeneas Aeneas.Std RustKopisSerial
open scoped BigOperators

set_option maxRecDepth 40000

namespace Kopis.Properties.NttMath

/-! ## The field -/

/-- The NTT prime `p`. -/
abbrev pN : ℕ := 50330113

/-- The coefficient field `ℤ/p` the transform works over. -/
abbrev Zp := ZMod pN

/-- Turn a numeric congruence mod `p` into an equation in `ℤ/p`. -/
theorem cast_eq_of_mod {a b : ℕ} (h : a % pN = b % pN) : ((a : Zp)) = (b : Zp) :=
  (ZMod.natCast_eq_natCast_iff' a b pN).mpr h

/-- `2³² mod p`, the Montgomery radix residue.  Used inside the `decide`d table checks; the
`ℤ/p`-level lemmas below spell it as a bare numeral so that `push_cast` normal forms match. -/
abbrev R32 : ℕ := 16907691
/-- `2⁶⁴ mod p`. -/
abbrev R64 : ℕ := 6122781

/-- The Montgomery-undoing scalar `2⁻³² ∈ ℤ/p`. -/
def Rinv : Zp := (8426221 : Zp)

/-- `2³² · 2⁻³² = 1` in `ℤ/p`. -/
theorem R32_Rinv : (16907691 : Zp) * Rinv = 1 := by
  have h : ((16907691 * 8426221 : ℕ) : Zp) = ((1 : ℕ) : Zp) := cast_eq_of_mod (by norm_num)
  push_cast at h
  rw [Rinv]
  exact h

/-- `2⁶⁴ · (2⁻³²)² = 1` in `ℤ/p`. -/
theorem R64_Rinv_sq : (6122781 : Zp) * Rinv ^ 2 = 1 := by
  have h : ((6122781 * (8426221 * 8426221) : ℕ) : Zp) = ((1 : ℕ) : Zp) :=
    cast_eq_of_mod (by norm_num)
  push_cast at h
  rw [Rinv]
  calc (6122781 : Zp) * (8426221 : Zp) ^ 2
      = 6122781 * (8426221 * 8426221) := by ring
    _ = 1 := h

/-! ## The `ZETAS` table as data

`ZN` is the shipped table read as naturals.  `zetas_val` is the only bridge to the extracted
array, and every algebraic fact below is a `decide`d numeric relation among `ZN`'s entries. -/

/-- The `ZETAS` table of `src/arithmetic/ntt.rs`, as naturals. -/
def ZN : List ℕ := [
  16907691, 2667794, 25435945, 38041794, 4526213, 35360986, 30701667, 21078350,
  36956843, 13677930, 22323069, 13735052, 16437056, 5691837, 29800035, 15764652,
  45309494, 32237400, 24236486, 2001600, 1321324, 27016828, 15167304, 4366839,
  28120194, 32421317, 30261273, 12292806, 22968316, 13702742, 937110, 2965954,
  34335133, 44939767, 6512044, 26419553, 19973946, 49111849, 40847418, 20023056,
  43261597, 41129446, 12627709, 45952874, 30150184, 36681813, 45532529, 39191671,
  45414311, 2081056, 808565, 49693071, 31006016, 28961757, 15337390, 31683976,
  4955339, 27911199, 29647313, 30189282, 40031443, 49298885, 46092656, 18408488,
  245475, 31889855, 39534436, 41714666, 8292132, 21449251, 22309987, 8205570,
  31096891, 47405297, 930348, 6971348, 10106150, 31035883, 46359140, 35263708,
  25740623, 9884444, 542513, 16415589, 9876654, 44372807, 21881921, 19165831,
  9227072, 2984297, 36824748, 43900147, 43917176, 9030513, 26543409, 34836022,
  45307234, 35198677, 14645063, 2098347, 37061938, 3244828, 41096247, 32062813,
  8918713, 47344810, 46288223, 21000897, 41046191, 20508021, 35242638, 21557502,
  49459492, 3469647, 1704205, 29274982, 27408601, 6834376, 3860969, 50170866,
  7253270, 26028155, 34019372, 9518412, 22713734, 14612739, 26018446, 43305093,
  12047271, 21217146, 26069968, 4256850, 3639874, 48691800, 17320569, 3323937,
  32443671, 42492417, 9308803, 33498296, 25236161, 17970048, 30529967, 11776789,
  23284408, 23725761, 39814592, 32816444, 45216211, 34497791, 1878200, 45702238,
  40014922, 39122569, 28779735, 44971151, 12142149, 25663462, 31479913, 19837380,
  39143843, 21323231, 17806070, 36807664, 47595478, 49950288, 16588490, 32773564,
  19315478, 33753056, 15093953, 23446825, 49044025, 41815538, 1288725, 23610193,
  2754751, 40030005, 13643238, 20793088, 16114388, 33147218, 15927487, 41781494,
  5795109, 11439966, 15064762, 35884894, 22645018, 10582966, 14900694, 21660678,
  16765530, 20825350, 30320649, 42368153, 39131901, 42360159, 6363984, 35581825,
  28072132, 11706419, 20970510, 44236552, 17934700, 14577479, 42770390, 44206858,
  28865919, 40187227, 15964209, 15444696, 17019703, 32900174, 28423607, 42332883,
  32435385, 40121202, 37968791, 33541227, 35393185, 34591081, 48852822, 8473545,
  43827986, 23231608, 34405552, 26405625, 27381101, 33514230, 46158701, 27741938,
  10409285, 21224207, 6796942, 35314909, 49625944, 20271219, 6354214, 38361969,
  34767461, 14097694, 13212224, 47820051, 49316243, 20113174, 21747171, 39170867,
  38847587, 20584729, 27124165, 40492847, 7742348, 43534070, 7422899, 12232461
]

theorem ZN_length : ZN.length = 256 := by decide

/-- Every table entry is a canonical residue, `< p`.  This is also what bounds the `i32`/`i64`
products in the butterflies. -/
def zn_lt_p : Bool := ZN.all (fun z => z < pN)

theorem zn_lt_p_true : zn_lt_p = true := by decide

theorem ZN_lt (k : ℕ) (hk : k < 256) : ZN[k]! < pN := by
  have h := zn_lt_p_true
  unfold zn_lt_p at h
  rw [List.all_eq_true] at h
  have hmem : ZN[k]! ∈ ZN := by
    rw [getElem!_pos ZN k (by rw [ZN_length]; exact hk)]
    exact List.getElem_mem _
  exact of_decide_eq_true (h _ hmem)

-- **The single bridge to the extracted code.**  The `ZETAS` array of `ExtractedRust.lean`
-- holds exactly `ZN`, entry for entry.  (`unseal` is needed because the extracted table is
-- marked `irreducible`.)
unseal arithmetic.ntt.ZETAS in
theorem zetas_list :
    List.map (fun (z : Std.I32) => z.val) (arithmetic.ntt.ZETAS).val
      = List.map (fun (n : ℕ) => (n : ℤ)) ZN := by
  decide

theorem zetas_len : (arithmetic.ntt.ZETAS).val.length = 256 := by simp

theorem zetas_val (k : ℕ) (hk : k < 256) :
    ((arithmetic.ntt.ZETAS).val[k]!).val = (ZN[k]! : ℤ) := by
  have h := congrArg (fun l => l[k]!) zetas_list
  have hl1 : (List.map (fun (z : Std.I32) => z.val) (arithmetic.ntt.ZETAS).val).length = 256 := by
    rw [List.length_map, zetas_len]
  have hl2 : (List.map (fun (n : ℕ) => (n : ℤ)) ZN).length = 256 := by
    rw [List.length_map, ZN_length]
  rw [getElem!_pos _ k (by rw [hl1]; exact hk), getElem!_pos _ k (by rw [hl2]; exact hk),
    List.getElem_map, List.getElem_map] at h
  rw [getElem!_pos _ k (by rw [zetas_len]; exact hk),
    getElem!_pos _ k (by rw [ZN_length]; exact hk)]
  exact h

/-! ## Plain (non-Montgomery) twiddles and the CRT-tree constants -/

/-- The plain value of table entry `k`.  The stored entry is `ζ_k · 2³²`, so the plain twiddle is
the entry times `2⁻³²` — exactly the factor a `mont_reduce (ZETAS[k] * x)` applies. -/
def zetaP (k : ℕ) : Zp := ((ZN[k]! : ℕ) : Zp) * Rinv

/-- The CRT-tree node constant: node `k` carries the modulus `X^m - cst k`.  The root is
`cst 1 = -1` (the ring `X²⁵⁶ + 1`); a node's two children carry `±` the twiddle that split it. -/
def cst (k : ℕ) : Zp :=
  if k = 1 then -1 else if k % 2 = 0 then zetaP (k / 2) else -(zetaP (k / 2))

theorem cst_one : cst 1 = -1 := rfl

theorem cst_even {k : ℕ} (_hk : 1 ≤ k) : cst (2 * k) = zetaP k := by
  unfold cst
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem cst_odd {k : ℕ} (hk : 1 ≤ k) : cst (2 * k + 1) = -(zetaP k) := by
  unfold cst
  rw [if_neg (by omega), if_neg (by omega)]
  congr 2
  omega

/-! ### The numeric table relations

Three `decide`d `Bool` checks over `ZN`, then their `ℤ/p` consequences. -/

/-- `ζ₁² = -1`: the root split of `X²⁵⁶ + 1`. -/
def rootOK : Bool := (ZN[1]! * ZN[1]! + R64) % pN == 0

/-- Child twiddles square to their parent's node constant: `ζ_{2k}² = c_{2k} = ζ_k` and
`ζ_{2k+1}² = c_{2k+1} = -ζ_k`, in plain form. -/
def treeOK : Bool :=
  (List.range 128).all (fun k =>
    k == 0 ||
    ((ZN[2 * k]! * ZN[2 * k]!) % pN == (ZN[k]! * R32) % pN &&
     (ZN[2 * k + 1]! * ZN[2 * k + 1]! + ZN[k]! * R32) % pN == 0))

/-- The inverse-transform pairing.  The Gentleman-Sande layer that undoes Cooley-Tukey butterfly
`k` reads table entry `k' = 3·2^j - 1 - k`, and `ζ_k · ζ_{k'} = -1`, so the `neg_zeta` the code
forms is exactly `ζ_k⁻¹`. -/
def pairOK : Bool :=
  (List.range 8).all (fun j =>
    (List.range (2 ^ j)).all (fun b =>
      (ZN[2 ^ j + b]! * ZN[3 * 2 ^ j - 1 - (2 ^ j + b)]! + R64) % pN == 0))

theorem rootOK_true : rootOK = true := by decide
theorem treeOK_true : treeOK = true := by decide
theorem pairOK_true : pairOK = true := by decide

/-- Convert a `decide`d `(a + b) % p = 0` into `(a : ℤ/p) = -(b : ℤ/p)`. -/
private theorem cast_neg_of_add_mod {a b : ℕ} (h : (a + b) % pN = 0) :
    ((a : ℕ) : Zp) = -((b : ℕ) : Zp) := by
  have hc : (((a + b : ℕ)) : Zp) = ((0 : ℕ) : Zp) :=
    cast_eq_of_mod (h.trans (Nat.zero_mod _).symm)
  push_cast at hc
  rw [eq_neg_iff_add_eq_zero]
  exact hc

/-- `ζ₁² = -1` in `ℤ/p`. -/
theorem zetaP_one_sq : zetaP 1 ^ 2 = -1 := by
  have h : (ZN[1]! * ZN[1]! + R64) % pN = 0 := by
    have hr := rootOK_true; unfold rootOK at hr; exact Nat.eq_of_beq_eq_true hr
  have hmul := cast_neg_of_add_mod h
  push_cast at hmul
  unfold zetaP
  calc (((ZN[1]! : ℕ) : Zp) * Rinv) ^ 2
      = (((ZN[1]! : ℕ) : Zp) * ((ZN[1]! : ℕ) : Zp)) * Rinv ^ 2 := by ring
    _ = (-(6122781 : Zp)) * Rinv ^ 2 := by rw [hmul]
    _ = -((6122781 : Zp) * Rinv ^ 2) := by ring
    _ = -1 := by rw [R64_Rinv_sq]

theorem treeOK_even {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 128) :
    (ZN[2 * k]! * ZN[2 * k]!) % pN = (ZN[k]! * R32) % pN := by
  have h := treeOK_true
  unfold treeOK at h
  rw [List.all_eq_true] at h
  have hk' := h k (by simp only [List.mem_range]; omega)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hk'
  rcases hk' with h0 | ⟨he, _⟩
  · omega
  · exact he

theorem treeOK_odd {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 128) :
    (ZN[2 * k + 1]! * ZN[2 * k + 1]! + ZN[k]! * R32) % pN = 0 := by
  have h := treeOK_true
  unfold treeOK at h
  rw [List.all_eq_true] at h
  have hk' := h k (by simp only [List.mem_range]; omega)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hk'
  rcases hk' with h0 | ⟨_, ho⟩
  · omega
  · exact ho

/-- **Child twiddles square to the node constant** — the fact that makes one butterfly layer a
CRT split.  Stated for every node index the network actually uses. -/
theorem zetaP_sq {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 256) : zetaP k ^ 2 = cst k := by
  rcases Nat.eq_or_lt_of_le hk1 with h1 | h1
  · rw [← h1, cst_one]; exact zetaP_one_sq
  · obtain ⟨j, hj⟩ : ∃ j, k / 2 = j := ⟨k / 2, rfl⟩
    have hj1 : 1 ≤ j := by omega
    have hj128 : j < 128 := by omega
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨t, ht⟩ := he
      have hkt : k = 2 * j := by omega
      subst hkt
      rw [cst_even hj1]
      have hc : ((ZN[2 * j]! * ZN[2 * j]! : ℕ) : Zp) = ((ZN[j]! * R32 : ℕ) : Zp) :=
        cast_eq_of_mod (treeOK_even hj1 hj128)
      push_cast at hc
      unfold zetaP
      calc (((ZN[2 * j]! : ℕ) : Zp) * Rinv) ^ 2
          = (((ZN[2 * j]! : ℕ) : Zp) * ((ZN[2 * j]! : ℕ) : Zp)) * Rinv ^ 2 := by ring
        _ = (((ZN[j]! : ℕ) : Zp) * (16907691 : Zp)) * Rinv ^ 2 := by rw [hc]
        _ = ((ZN[j]! : ℕ) : Zp) * ((16907691 : Zp) * Rinv) * Rinv := by ring
        _ = ((ZN[j]! : ℕ) : Zp) * Rinv := by rw [R32_Rinv]; ring
    · obtain ⟨t, ht⟩ := ho
      have hkt : k = 2 * j + 1 := by omega
      subst hkt
      rw [cst_odd hj1]
      have hmul := cast_neg_of_add_mod (treeOK_odd hj1 hj128)
      push_cast at hmul
      unfold zetaP
      calc (((ZN[2 * j + 1]! : ℕ) : Zp) * Rinv) ^ 2
          = (((ZN[2 * j + 1]! : ℕ) : Zp) * ((ZN[2 * j + 1]! : ℕ) : Zp)) * Rinv ^ 2 := by ring
        _ = (-(((ZN[j]! : ℕ) : Zp) * (16907691 : Zp))) * Rinv ^ 2 := by rw [hmul]
        _ = -(((ZN[j]! : ℕ) : Zp) * ((16907691 : Zp) * Rinv) * Rinv) := by ring
        _ = -(((ZN[j]! : ℕ) : Zp) * Rinv) := by rw [R32_Rinv]; ring

/-- **The Gentleman-Sande pairing.**  `ζ_{nb+b} · ζ_{2·nb-1-b} = -1`, so the `neg_zeta` the
inverse loop forms from entry `2·nb-1-b` is the inverse of the twiddle the forward loop used at
the matching butterfly. -/
theorem zetaP_pair {nb b : ℕ} (hnb : ∃ j, j < 8 ∧ nb = 2 ^ j) (hb : b < nb) :
    zetaP (nb + b) * zetaP (2 * nb - 1 - b) = -1 := by
  obtain ⟨j, hj, rfl⟩ := hnb
  have h := pairOK_true
  unfold pairOK at h
  rw [List.all_eq_true] at h
  have hj' := h j (by simp only [List.mem_range]; omega)
  rw [List.all_eq_true] at hj'
  have hb' := hj' b (by simp only [List.mem_range]; omega)
  simp only [beq_iff_eq] at hb'
  rw [show 3 * 2 ^ j - 1 - (2 ^ j + b) = 2 * 2 ^ j - 1 - b by omega] at hb'
  have hmul := cast_neg_of_add_mod hb'
  push_cast at hmul
  unfold zetaP
  calc (((ZN[2 ^ j + b]! : ℕ) : Zp) * Rinv) * (((ZN[2 * 2 ^ j - 1 - b]! : ℕ) : Zp) * Rinv)
      = (((ZN[2 ^ j + b]! : ℕ) : Zp) * ((ZN[2 * 2 ^ j - 1 - b]! : ℕ) : Zp)) * Rinv ^ 2 := by ring
    _ = (-(6122781 : Zp)) * Rinv ^ 2 := by rw [hmul]
    _ = -((6122781 : Zp) * Rinv ^ 2) := by ring
    _ = -1 := by rw [R64_Rinv_sq]

/-- A node constant squares to its parent's: `c_{2k} = γ` and `c_{2k+1} = -γ` both square to
`γ² = c_k`.  Iterated, this gives every leaf `c²⁵⁶ = c₁ = -1`. -/
theorem cst_sq {j : ℕ} (hj : 2 ≤ j) (hj2 : j < 512) : cst j ^ 2 = cst (j / 2) := by
  obtain ⟨k, hk⟩ : ∃ k, j / 2 = k := ⟨j / 2, rfl⟩
  have hk1 : 1 ≤ k := by omega
  have hk256 : k < 256 := by omega
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨t, ht⟩ := he
    have hjk : j = 2 * k := by omega
    subst hjk
    rw [cst_even hk1, zetaP_sq hk1 hk256, hk]
  · obtain ⟨t, ht⟩ := ho
    have hjk : j = 2 * k + 1 := by omega
    subst hjk
    have hsq : (-(zetaP k)) ^ 2 = zetaP k ^ 2 := by ring
    rw [cst_odd hk1, hsq, zetaP_sq hk1 hk256, hk]

/-- **Every leaf constant satisfies `c²⁵⁶ = -1`** — i.e. `X - c_{256+b}` really divides
`X²⁵⁶ + 1`, which is what makes evaluation at `c_{256+b}` a ring homomorphism out of the
negacyclic ring. -/
theorem cst_leaf_pow (b : ℕ) (hb : b < 256) : cst (256 + b) ^ 256 = -1 := by
  have step : ∀ (d j : ℕ), 2 ^ d ≤ j → j < 2 ^ (d + 1) → j < 512 → cst j ^ (2 ^ d) = cst 1 := by
    intro d
    induction d with
    | zero =>
      intro j h1 h2 _
      have e1 : (2 : ℕ) ^ 0 = 1 := rfl
      have e2 : (2 : ℕ) ^ (0 + 1) = 2 := rfl
      have hj : j = 1 := by omega
      rw [hj, e1, pow_one]
    | succ d ih =>
      intro j h1 h2 h3
      have hpd : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by norm_num)
      have hsplit : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      have hsplit2 : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
      have hj2 : 2 ≤ j := by omega
      have hdiv1 : 2 ^ d ≤ j / 2 := by omega
      have hdiv2 : j / 2 < 2 ^ (d + 1) := by omega
      have hpow : cst j ^ (2 ^ (d + 1)) = (cst j ^ 2) ^ (2 ^ d) := by
        rw [← pow_mul, ← hsplit]
      rw [hpow, cst_sq hj2 h3]
      exact ih (j / 2) hdiv1 hdiv2 (by omega)
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have e9 : (2 : ℕ) ^ (8 + 1) = 512 := by norm_num
  have h := step 8 (256 + b) (by omega) (by omega) (by omega)
  rw [e8] at h
  rw [h, cst_one]

/-! ## The transform invariant -/

/-- Splitting a `range (2n)` sum into its even and odd halves — the combinatorial heart of both
butterfly-layer lemmas. -/
theorem sum_range_two (n : ℕ) (g : ℕ → Zp) :
    ∑ q ∈ Finset.range (2 * n), g q
      = (∑ q ∈ Finset.range n, g (2 * q)) + ∑ q ∈ Finset.range n, g (2 * q + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- **The transform invariant.**  `State nb m c f a` says the array `a` holds, scaled by `c`, the
CRT image of `f` at the tree level with `nb` blocks of size `m`: block `b` sits at offset `b·m`
and holds the coefficients of `f mod (X^m - cst (nb + b))`.

`State 1 256 1 f a` says `a = f` (the untransformed input); `State 256 1 1 f a` says `a b` is the
evaluation of `f` at the `b`-th leaf constant (the fully transformed output). -/
def State (nb m : ℕ) (c : Zp) (f a : ℕ → Zp) : Prop :=
  ∀ b < nb, ∀ r < m,
    a (b * m + r) = c * ∑ q ∈ Finset.range nb, f (q * m + r) * cst (nb + b) ^ q

/-- The untransformed state: one block of size 256 is just `c • f`. -/
theorem State_root {c : Zp} {f a : ℕ → Zp} (h : State 1 256 c f a) (r : ℕ) (hr : r < 256) :
    a r = c * f r := by
  have := h 0 (by norm_num) r hr
  simpa using this

/-- Building the untransformed state from `a = c • f`. -/
theorem State_root_intro {c : Zp} {f a : ℕ → Zp} (h : ∀ r < 256, a r = c * f r) :
    State 1 256 c f a := by
  intro b hb r hr
  have hb0 : b = 0 := by omega
  subst hb0
  simpa using h r hr

/-- The fully transformed state: `a b` is `c` times the evaluation of `f` at leaf `b`. -/
theorem State_leaf {c : Zp} {f a : ℕ → Zp} (h : State 256 1 c f a) (b : ℕ) (hb : b < 256) :
    a b = c * ∑ i ∈ Finset.range 256, f i * cst (256 + b) ^ i := by
  have := h b hb 0 (by norm_num)
  simpa using this

/-- **One Cooley-Tukey layer.**  Splitting each block of size `2m'` in two with the twiddle
`zetaP (nb + b)` refines the CRT factorisation by one level. -/
theorem State_ct {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    {c : Zp} {f a a' : ℕ → Zp}
    (hst : State nb (2 * m') c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r)
          = a (b * (2 * m') + r) + zetaP (nb + b) * a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
          = a (b * (2 * m') + r) - zetaP (nb + b) * a (b * (2 * m') + m' + r)) :
    State (2 * nb) m' c f a' := by
  intro b' hb' r hr
  obtain ⟨b, hb, hhalf⟩ : ∃ b, b < nb ∧ (b' = 2 * b ∨ b' = 2 * b + 1) :=
    ⟨b' / 2, by omega, by omega⟩
  have hk1 : 1 ≤ nb + b := by omega
  have hk256 : nb + b < 256 := by omega
  have hγ2 : zetaP (nb + b) ^ 2 = cst (nb + b) := zetaP_sq hk1 hk256
  have hlo := hst b hb r (by omega)
  have hhi := hst b hb (m' + r) (by omega)
  have hidx : b * (2 * m') + (m' + r) = b * (2 * m') + m' + r := by ring
  rw [hidx] at hhi
  -- the even/odd split of a child sum, for either child constant `δ` with `δ² = cst (nb+b)`
  have key : ∀ δ : Zp, δ ^ 2 = cst (nb + b) →
      ∑ q ∈ Finset.range (2 * nb), f (q * m' + r) * δ ^ q
        = (∑ q ∈ Finset.range nb, f (q * (2 * m') + r) * cst (nb + b) ^ q)
          + δ * ∑ q ∈ Finset.range nb, f (q * (2 * m') + (m' + r)) * cst (nb + b) ^ q := by
    intro δ hδ
    rw [sum_range_two nb (fun q => f (q * m' + r) * δ ^ q), Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [show 2 * q * m' + r = q * (2 * m') + r by ring, ← hδ, ← pow_mul]
    · refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [show (2 * q + 1) * m' + r = q * (2 * m') + (m' + r) by ring, ← hδ, pow_succ, ← pow_mul]
      ring
  have hnegsq : (-(zetaP (nb + b))) ^ 2 = cst (nb + b) := by
    rw [show (-(zetaP (nb + b))) ^ 2 = zetaP (nb + b) ^ 2 by ring]; exact hγ2
  rcases hhalf with rfl | rfl
  · rw [show 2 * b * m' + r = b * (2 * m') + r by ring, (hbut b hb r hr).1, hlo, hhi,
      show 2 * nb + 2 * b = 2 * (nb + b) by ring, cst_even hk1, key (zetaP (nb + b)) hγ2]
    ring
  · rw [show (2 * b + 1) * m' + r = b * (2 * m') + m' + r by ring, (hbut b hb r hr).2, hlo, hhi,
      show 2 * nb + (2 * b + 1) = 2 * (nb + b) + 1 by ring, cst_odd hk1,
      key (-(zetaP (nb + b))) hnegsq]
    ring

/-- **One Gentleman-Sande layer.**  Merging block pairs performs the inverse CRT reconstruction,
up to the factor `2` the layer leaves behind (eight of which `INVNTT_SCALE` cancels).  The
`neg_zeta` the code forms from table entry `2·nb-1-b` is `ζ_{nb+b}⁻¹`, by `zetaP_pair`. -/
theorem State_gs {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    (hpow : ∃ j, j < 8 ∧ nb = 2 ^ j)
    {c : Zp} {f a a' : ℕ → Zp}
    (hst : State (2 * nb) m' c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r)
          = a (b * (2 * m') + r) + a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
          = (-(zetaP (2 * nb - 1 - b))) * (a (b * (2 * m') + r) - a (b * (2 * m') + m' + r))) :
    State nb (2 * m') (2 * c) f a' := by
  intro b hb s hs
  have hk1 : 1 ≤ nb + b := by omega
  have hk256 : nb + b < 256 := by omega
  have hγ2 : zetaP (nb + b) ^ 2 = cst (nb + b) := zetaP_sq hk1 hk256
  have hδ : -(zetaP (2 * nb - 1 - b)) * zetaP (nb + b) = 1 := by
    have h := zetaP_pair hpow hb
    rw [neg_mul, mul_comm, h, neg_neg]
  -- the two child blocks: index `2b` (constant `γ`) and `2b+1` (constant `-γ`)
  have hclo : ∀ t < m', a (b * (2 * m') + t)
      = c * ∑ q ∈ Finset.range (2 * nb), f (q * m' + t) * zetaP (nb + b) ^ q := by
    intro t ht
    have h := hst (2 * b) (by omega) t ht
    rwa [show 2 * b * m' + t = b * (2 * m') + t by ring,
      show 2 * nb + 2 * b = 2 * (nb + b) by ring, cst_even hk1] at h
  have hchi : ∀ t < m', a (b * (2 * m') + m' + t)
      = c * ∑ q ∈ Finset.range (2 * nb), f (q * m' + t) * (-(zetaP (nb + b))) ^ q := by
    intro t ht
    have h := hst (2 * b + 1) (by omega) t ht
    rwa [show (2 * b + 1) * m' + t = b * (2 * m') + m' + t by ring,
      show 2 * nb + (2 * b + 1) = 2 * (nb + b) + 1 by ring, cst_odd hk1] at h
  have hsplit : ∀ (δ : Zp) (t : ℕ),
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
  have hgsq : ((-(zetaP (nb + b))) ^ 2) = cst (nb + b) := by
    rw [show (-(zetaP (nb + b))) ^ 2 = zetaP (nb + b) ^ 2 by ring]; exact hγ2
  rcases lt_or_ge s m' with hslt | hsge
  · have hlo := hclo s hslt
    have hhi := hchi s hslt
    rw [hsplit (zetaP (nb + b)) s, hγ2] at hlo
    rw [hsplit (-(zetaP (nb + b))) s, hgsq] at hhi
    rw [(hbut b hb s hslt).1, hlo, hhi]
    ring
  · obtain ⟨t, rfl⟩ : ∃ t, s = m' + t := ⟨s - m', by omega⟩
    have ht : t < m' := by omega
    have hlo := hclo t ht
    have hhi := hchi t ht
    rw [hsplit (zetaP (nb + b)) t, hγ2] at hlo
    rw [hsplit (-(zetaP (nb + b))) t, hgsq] at hhi
    rw [show b * (2 * m') + (m' + t) = b * (2 * m') + m' + t by ring,
      (hbut b hb t ht).2, hlo, hhi]
    have hexp : ∀ A B : Zp,
        (-(zetaP (2 * nb - 1 - b))) * (c * (A + zetaP (nb + b) * B)
            - c * (A + (-(zetaP (nb + b))) * B))
          = ((-(zetaP (2 * nb - 1 - b))) * zetaP (nb + b)) * (2 * c * B) := by
      intro A B; ring
    rw [hexp, hδ, one_mul]

/-! ## The convolution theorem -/

/-- The negacyclic convolution of two length-256 coefficient functions: `X²⁵⁶ = -1`, so a product
`f i · g j` lands on coefficient `(i+j) mod 256` with a sign flip when `i + j ≥ 256`.  This
mirrors the spec's `Spec.Kopis.Polynomial.mul`. -/
def nconv (f g : ℕ → Zp) (n : ℕ) : Zp :=
  ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
    if i + j = n then f i * g j else if i + j = n + 256 then -(f i * g j) else 0

/-- **The convolution theorem.**  Evaluation at any `c` with `c²⁵⁶ = -1` is a ring homomorphism
out of the negacyclic ring: the pointwise product of two transforms is the transform of the
negacyclic product.  With `cst_leaf_pow` this is what makes the NTT compute a ring
multiplication. -/
theorem Ev_nconv (f g : ℕ → Zp) {c : Zp} (hc : c ^ 256 = -1) :
    (∑ i ∈ Finset.range 256, f i * c ^ i) * (∑ j ∈ Finset.range 256, g j * c ^ j)
      = ∑ n ∈ Finset.range 256, nconv f g n * c ^ n := by
  -- for fixed `(i, j)` exactly one `n < 256` contributes, and it gives `f i · g j · c^(i+j)`
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

/-! ## The convolution as a single sum

`nconv` is stated as a double sum because that is the shape `Ev_nconv`'s proof wants.  For every
other purpose the inner sum has exactly one surviving term — given `n < 256` and `i < 256` the
partner index is forced to be `n - i` or `n + 256 - i` — so it collapses to `nconvR`, a single
sum of 256 products.

`nconvR` is stated over an arbitrary commutative ring on purpose.  The bridge has to compare
*three* readings of the same convolution: over `ℤ` (where the exactness bound lives), over `ℤ/p`
(where the transform computes), and over `ℤ/2¹⁶` (where the specification's answer lives).  With
one polymorphic definition the first is carried into the other two by `nconvR_map`, a one-line
consequence of `map_sum`, instead of by two separate re-derivations. -/

/-- The negacyclic convolution of two length-256 coefficient functions, as a single sum:
coefficient `n` collects `F i · G (n-i)` for `i ≤ n` and `-F i · G (n+256-i)` for `i > n`, the
sign flip being `X²⁵⁶ = -1`. -/
def nconvR {R : Type*} [CommRing R] (F G : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range 256, F i * (if i ≤ n then G (n - i) else -(G (n + 256 - i)))

/-- The double sum of `nconv` collapses to the single sum of `nconvR`. -/
theorem nconv_eq_nconvR (f g : ℕ → Zp) (n : ℕ) (hn : n < 256) :
    nconv f g n = nconvR f g n := by
  unfold nconv nconvR
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < 256 := Finset.mem_range.mp hi
  by_cases hle : i ≤ n
  · rw [if_pos hle, Finset.sum_eq_single (n - i)]
    · rw [if_pos (by omega)]
    · intro j hj hne
      have hj' : j < 256 := Finset.mem_range.mp hj
      rw [if_neg (by omega), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega : n - i < 256)) h
  · rw [if_neg hle, Finset.sum_eq_single (n + 256 - i)]
    · rw [if_neg (by omega), if_pos (by omega)]; ring
    · intro j hj hne
      have hj' : j < 256 := Finset.mem_range.mp hj
      rw [if_neg (by omega), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega : n + 256 - i < 256)) h

/-- `nconvR` at `n < 256` reads its arguments only at indices below 256. -/
theorem nconvR_congr {R : Type*} [CommRing R] {F F' G G' : ℕ → R} {n : ℕ} (hn : n < 256)
    (hF : ∀ i, i < 256 → F i = F' i) (hG : ∀ j, j < 256 → G j = G' j) :
    nconvR F G n = nconvR F' G' n := by
  unfold nconvR
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < 256 := Finset.mem_range.mp hi
  rw [hF i hi']
  congr 1
  split_ifs with hle
  · exact hG _ (by omega)
  · rw [hG _ (by omega)]

/-- The integer convolution casts into any commutative ring coefficientwise.  This is the bridge
between the exactness bound (over `ℤ`) and the two quotients the proof works in. -/
theorem nconvR_intCast {R : Type*} [CommRing R] (F G : ℕ → ℤ) (n : ℕ) :
    ((nconvR F G n : ℤ) : R)
      = nconvR (fun i => ((F i : ℤ) : R)) (fun j => ((G j : ℤ) : R)) n := by
  unfold nconvR
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Int.cast_mul]
  congr 1
  split_ifs
  · rfl
  · rw [Int.cast_neg]

/-- A ring homomorphism carries `nconvR` to `nconvR` of the transported coefficients.  This is
what relates the integer convolution to its `ℤ/p` and `ℤ/2¹⁶` readings. -/
theorem nconvR_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (F G : ℕ → R) (n : ℕ) :
    φ (nconvR F G n) = nconvR (fun i => φ (F i)) (fun j => φ (G j)) n := by
  unfold nconvR
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul]
  congr 1
  split_ifs
  · rfl
  · rw [map_neg]

/-- **The exactness bound.**  Each output coefficient of an integer negacyclic convolution is a
sum of 256 products, so it is bounded by `256 · bF · bG`.  With `bF = 2¹³-1` and `bG = μ/2` this
is what `fitsExactly` compares against `p/2`. -/
theorem abs_nconvR_le {F G : ℕ → ℤ} {bF bG : ℤ} {n : ℕ} (hn : n < 256)
    (hF : ∀ i, i < 256 → |F i| ≤ bF) (hG : ∀ j, j < 256 → |G j| ≤ bG) :
    |nconvR F G n| ≤ 256 * bF * bG := by
  have hbF : 0 ≤ bF := le_trans (abs_nonneg _) (hF 0 (by omega))
  have hterm : ∀ i ∈ Finset.range 256,
      |F i * (if i ≤ n then G (n - i) else -(G (n + 256 - i)))| ≤ bF * bG := by
    intro i hi
    have hi' : i < 256 := Finset.mem_range.mp hi
    rw [abs_mul]
    refine mul_le_mul (hF i hi') ?_ (abs_nonneg _) hbF
    split_ifs with h
    · exact hG _ (by omega)
    · rw [abs_neg]; exact hG _ (by omega)
  calc |nconvR F G n| ≤ ∑ i ∈ Finset.range 256,
        |F i * (if i ≤ n then G (n - i) else -(G (n + 256 - i)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range 256, bF * bG := Finset.sum_le_sum hterm
    _ = 256 * bF * bG := by rw [Finset.sum_const, Finset.card_range]; push_cast; ring

end Kopis.Properties.NttMath
