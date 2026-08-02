import Kopis.Properties.SerializeTop
open Aeneas Aeneas.Std Result RustKopisSerial
open Spec (𝔹)
open scoped BigOperators
namespace Kopis.Properties
open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-! # `Matrix.serialize` correctness (Y = 1 / column case).

Proves the Aeneas-extracted `arithmetic.matrix_arith.Matrix.serialize` matches
the spec `Spec.Kopis.PolyVector.serialize` for the `Y = 1` matrices used by the
public key. -/

/-- Abstraction of a `Matrix L 1` as a spec `PolyVector` of length `L`. -/
def toVecN (n : ℕ) {L : Usize} (self : arithmetic.matrix_arith.Matrix L 1#usize) :
    Spec.Kopis.PolyVector (2 ^ n) L.val :=
  Vector.ofFn fun (a : Fin L.val) => toPolyN n ((self.val[a.val]!).val[0]!)

/-- If `q` lies in the `row`-th block of width `m`, then `q / m = row` and
`q % m = q - row * m`. -/
private theorem div_mod_of_range {m row q : ℕ} (hm : 0 < m)
    (h1 : row * m ≤ q) (h2 : q < (row + 1) * m) : q / m = row ∧ q % m = q - row * m := by
  have hexp : (row + 1) * m = row * m + m := by ring
  have hlt : q - row * m < m := by omega
  have heq : q = m * row + (q - row * m) := by rw [Nat.mul_comm]; omega
  have hd : q / m = row := by rw [heq, Nat.mul_add_div hm, Nat.div_eq_of_lt hlt, Nat.add_zero]
  refine ⟨hd, ?_⟩
  have hdm := Nat.div_add_mod q m
  rw [hd] at hdm
  have hc : m * row = row * m := Nat.mul_comm m row
  omega

/-- The `q`-th byte of `sliceToBytes s m h` is the `bv` of the `q`-th physical byte. -/
private theorem sliceToBytes_getElem! (s : Slice U8) (m : ℕ) (h : s.length = m) (q : ℕ) (hq : q < m) :
    (sliceToBytes s m h)[q]'hq = (s.val[q]!).bv := by
  simp only [sliceToBytes, Vector.getElem_ofFn]
  rw [getElem!_pos s.val q (by have hh : s.val.length = m := h; omega)]

/-- Inner loop of `Matrix.serialize` for `Y = 1`: fixed row `i`, iterating over the
single column `j ∈ [start, 1)`.  On `start = 0` it serializes `self[i][0]` into the
`i`-th `32n`-byte chunk; otherwise it leaves the buffer untouched. -/
theorem serialize_col_inner_spec {L : Usize}
    (iter : core.ops.range.Range Usize)
    (self : arithmetic.matrix_arith.Matrix L 1#usize) (out_buf : Slice U8)
    (bits chunk_len : Usize) (i : Usize) (n : ℕ)
    (hn : bits.val = n) (hrng : 1 ≤ n ∧ n ≤ 13) (hchunk : chunk_len.val = 32 * n)
    (hi : i.val < L.val) (hlen : out_buf.length = L.val * (32 * n))
    (hstart : iter.start.val ≤ 1) (hend : iter.«end».val = 1) :
    arithmetic.matrix_arith.Matrix.serialize_loop0_loop0 iter self out_buf bits chunk_len i
      ⦃ (p : (arithmetic.matrix_arith.Matrix L 1#usize) × (Slice U8)) =>
          p.1 = self ∧ ∃ _h : p.2.length = L.val * (32 * n),
            ∀ q, q < L.val * (32 * n) →
              (p.2.val[q]!).bv
                = if iter.start.val = 0 ∧ i.val * (32 * n) ≤ q ∧ q < (i.val + 1) * (32 * n)
                  then (Spec.Kopis.serialize n (toPolyN n ((self.val[i.val]!).val[0]!)))[q - i.val * (32 * n)]!
                  else (out_buf.val[q]!).bv ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.serialize_loop0_loop0
  have hm : 0 < 32 * n := by omega
  have hbufmax : L.val * (32 * n) ≤ Usize.max := hlen ▸ out_buf.property
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hstart0 : iter.start.val = 0 := by scalar_tac
    have hik : ∀ k, k ≤ L.val → k * (32 * n) ≤ Usize.max :=
      fun k hk => le_trans (Nat.mul_le_mul_right (32 * n) hk) hbufmax
    -- arithmetic on the chunk boundaries
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (show i.val * (1#usize).val ≤ Usize.max from by scalar_tac)
    have hi1v : i1.val = i.val := by rw [hi1]; simp
    let* ⟨ idx, hidx ⟩ ← Std.Usize.add_spec (show i1.val + iter.start.val ≤ Usize.max from by
      rw [hi1v, hstart0]
      simpa using le_trans (le_trans (le_of_lt hi) (Nat.le_mul_of_pos_right _ hm)) hbufmax)
    have hidxv : idx.val = i.val := by omega
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (show idx.val * chunk_len.val ≤ Usize.max from by
      rw [hidxv, hchunk]; exact hik i.val (le_of_lt hi))
    have hi2v : i2.val = i.val * (32 * n) := by rw [hi2, hidxv, hchunk]
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (show idx.val + (1#usize).val ≤ Usize.max from by
      rw [hidxv]
      simpa using le_trans (le_trans (show i.val + 1 ≤ L.val by omega) (Nat.le_mul_of_pos_right _ hm)) hbufmax)
    have hi3v : i3.val = i.val + 1 := by rw [hi3, hidxv]
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.mul_spec (show i3.val * chunk_len.val ≤ Usize.max from by
      rw [hi3v, hchunk]; exact hik (i.val + 1) (by omega))
    have hi4v : i4.val = (i.val + 1) * (32 * n) := by rw [hi4, hi3v, hchunk]
    have hi4eq : i4.val = i2.val + 32 * n := by rw [hi4v, hi2v]; try ring
    have h_i2i4 : i2.val ≤ i4.val := by rw [hi2v, hi4v]; exact Nat.mul_le_mul_right (32 * n) (by omega)
    have h_i4len : i4.val ≤ out_buf.length := by
      rw [hi4v, hlen]; exact Nat.mul_le_mul_right (32 * n) (by omega)
    have h_i4len' : i4.val ≤ out_buf.val.length := by rw [← Slice.length]; exact h_i4len
    -- the sub-slice write via index_mut
    have himspec :
        (core.slice.index.SliceIndexRangeUsizeSlice.index_mut
          ({ start := i2, «end» := i4 } : core.ops.range.Range Usize) out_buf)
        ⦃ (p : Slice U8 × (Slice U8 → Slice U8)) =>
            p.1.length = 32 * n ∧
            (∀ s' : Slice U8, (p.2 s').val = List.setSlice! out_buf.val i2.val s'.val) ⦄ := by
      simp only [core.slice.index.SliceIndexRangeUsizeSlice.index_mut, UScalar.le_equiv]
      rw [if_pos ⟨h_i2i4, h_i4len⟩]
      simp only [WP.spec_ok]
      refine ⟨?_, ?_⟩
      · show (out_buf.val.slice i2.val i4.val).length = 32 * n
        rw [List.slice_length]; omega
      · intro s'; trivial
    let* ⟨ out_chunk, index_mut_back, hoclen, hback ⟩ ← himspec
    have hself_len : self.val.length = L.val := self.property
    have hb1 : i.val < self.val.length := lt_of_lt_of_eq hi hself_len.symm
    let* ⟨ a, ha ⟩ ← Array.index_usize_spec self i hb1
    have ha_len : a.val.length = 1 := a.property
    have hrs : iter.start.val < a.val.length := lt_of_lt_of_eq (show iter.start.val < 1 by omega) ha_len.symm
    let* ⟨ re, hre ⟩ ← Array.index_usize_spec a iter.start hrs
    have hre_eq : re = (self.val[i.val]!).val[0]! := by
      have ea : self.val[i.val]! = a := (getElem!_pos self.val i.val hb1).trans ha.symm
      rw [ea, hre, ← getElem!_pos a.val iter.start.val hrs, hstart0]
    let* ⟨ out_chunk1, hoc_len, hoc_eq ⟩ ← ring_serialize_spec re out_chunk bits n hn hrng hoclen
    have hoc_len' : out_chunk1.val.length = 32 * n := hoc_len
    -- per-byte value of the freshly serialized chunk
    have hserbyte : ∀ k, k < 32 * n → (out_chunk1.val[k]!).bv
        = (Spec.Kopis.serialize n (toPolyN n re))[k]! := by
      intro k hk
      rw [getElem!_pos (Spec.Kopis.serialize n (toPolyN n re)) k hk,
        ← hoc_eq, sliceToBytes_getElem! out_chunk1 (32 * n) hoc_len k hk]
    have hlen1 : (index_mut_back out_chunk1).length = L.val * (32 * n) := by
      have hb := hback out_chunk1
      have : (index_mut_back out_chunk1).val.length = L.val * (32 * n) := by
        rw [hb, List.length_setSlice!]; exact hlen
      exact this
    -- since `Y = 1`, the loop makes exactly one iteration: `iter1 = {1, 1}` terminates.
    unfold arithmetic.matrix_arith.Matrix.serialize_loop0_loop0
    let* ⟨ o2, iter2, hnone2, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec iter1
      (show iter1.start.val ≥ iter1.«end».val by rw [hstart', hend']; omega)
    rw [hnone2]; simp only [WP.spec_ok]
    refine ⟨trivial, hlen1, ?_⟩
    intro q hq
    have hqbuf : q < out_buf.val.length := by
      have hh : out_buf.val.length = L.val * (32 * n) := hlen; omega
    rw [hback out_chunk1, hstart0]
    by_cases hrange : i2.val ≤ q ∧ q < i2.val + 32 * n
    · rw [List.getElem!_setSlice!_middle out_buf.val out_chunk1.val i2.val q
          ⟨hrange.1, by rw [hoc_len']; omega, hqbuf⟩,
        if_pos ⟨rfl, by rw [← hi2v]; exact hrange.1, by rw [← hi4v, hi4eq]; exact hrange.2⟩]
      rw [hserbyte (q - i2.val) (by omega), hre_eq, hi2v]
    · rw [List.getElem!_setSlice!_same out_buf.val out_chunk1.val i2.val q (by rw [hoc_len']; omega),
        if_neg (by rintro ⟨_, h1, h2⟩; exact hrange ⟨by rw [hi2v]; exact h1, by rw [← hi4eq, hi4v]; exact h2⟩)]
  · let* ⟨ o, iter1, hnone, hiter1 ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    have hs1 : iter.start.val = 1 := by scalar_tac
    refine ⟨trivial, hlen, ?_⟩
    intro q hq
    rw [if_neg (by rintro ⟨h0, _⟩; omega)]

/-- Outer loop of `Matrix.serialize` for `Y = 1`: iterating over rows `i ∈ [start, L)`.
Rows `≥ start` are freshly serialized; rows `< start` keep their old bytes. -/
theorem serialize_col_outer_spec {L : Usize}
    (iter : core.ops.range.Range Usize)
    (self : arithmetic.matrix_arith.Matrix L 1#usize) (out_buf : Slice U8)
    (bits chunk_len : Usize) (n : ℕ)
    (hn : bits.val = n) (hrng : 1 ≤ n ∧ n ≤ 13) (hchunk : chunk_len.val = 32 * n)
    (hlen : out_buf.length = L.val * (32 * n))
    (hstart : iter.start.val ≤ L.val) (hend : iter.«end».val = L.val) :
    arithmetic.matrix_arith.Matrix.serialize_loop0 iter self out_buf bits chunk_len
      ⦃ (r : Slice U8) => ∃ _h : r.length = L.val * (32 * n),
          ∀ q, q < L.val * (32 * n) →
            (r.val[q]!).bv
              = if iter.start.val ≤ q / (32 * n)
                then (Spec.Kopis.serialize n (toPolyN n ((self.val[q / (32 * n)]!).val[0]!)))[q % (32 * n)]!
                else (out_buf.val[q]!).bv ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.serialize_loop0
  have hm : 0 < 32 * n := by omega
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < L.val := by scalar_tac
    let* ⟨ self1, out_buf1, hself1, hlen1, hob1 ⟩ ←
      serialize_col_inner_spec { start := 0#usize, «end» := 1#usize } self out_buf bits chunk_len
        iter.start n hn hrng hchunk hi_lt hlen (by simp) (by simp)
    rw [hself1]
    apply WP.spec_mono
      (serialize_col_outer_spec iter1 self out_buf1 bits chunk_len n hn hrng hchunk hlen1
        (by rw [hstart']; scalar_tac) (by rw [hend']; exact hend))
    intro r hr
    obtain ⟨hrlen, hrq⟩ := hr
    refine ⟨hrlen, ?_⟩
    intro q hq
    rw [hrq q hq, hstart', hob1 q hq]
    set R := q / (32 * n) with hR
    set row0 := iter.start.val with hrow0
    have key : R * (32 * n) + q % (32 * n) = q := by rw [hR]; exact Nat.div_add_mod' q (32 * n)
    have hmod : q % (32 * n) < 32 * n := Nat.mod_lt _ hm
    by_cases hAB : row0 ≤ R
    · by_cases hBC : row0 + 1 ≤ R
      · rw [if_pos hBC, if_pos hAB]
      · have hReq : R = row0 := by omega
        rw [if_neg hBC, if_pos hAB]
        have hrange : row0 * (32 * n) ≤ q ∧ q < (row0 + 1) * (32 * n) := by
          rw [show (row0 + 1) * (32 * n) = row0 * (32 * n) + 32 * n from by ring]
          rw [← hReq]; omega
        rw [if_pos ⟨trivial, hrange.1, hrange.2⟩]
        have hqm := (div_mod_of_range hm hrange.1 hrange.2).2
        rw [hReq, hqm]
    · have hRlt : R < row0 := by omega
      have hqlt : q < row0 * (32 * n) := by
        have h1 : q < (R + 1) * (32 * n) := by
          rw [show (R + 1) * (32 * n) = R * (32 * n) + 32 * n from by ring]; omega
        exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right (32 * n) (by omega))
      rw [if_neg (by omega), if_neg (by rintro ⟨_, h1, _⟩; omega), if_neg hAB]
  · let* ⟨ o, iter1, hnone, hiter1 ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    have hge : iter.start.val = L.val := by scalar_tac
    refine ⟨hlen, ?_⟩
    intro q hq
    rw [if_neg (by rw [hge]; rw [Nat.not_le, Nat.div_lt_iff_lt_mul hm]; exact hq)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- **Correctness of `Matrix::serialize` for `Y = 1` (public-key column case).**
Serializing an `L × 1` matrix with `n`-bit coefficients produces the spec
`PolyVector.serialize n (toVecN n self)`. -/
theorem matrix_serialize_col_spec {L : Usize}
    (self : arithmetic.matrix_arith.Matrix L 1#usize)
    (out : Slice U8) (bits : Usize) (n : ℕ)
    (hn : bits.val = n) (hrng : 1 ≤ n ∧ n ≤ 13)
    (hlen : out.val.length = L.val * (32 * n))
    (hfit : L.val * n * 256 ≤ Usize.max) :
    arithmetic.matrix_arith.Matrix.serialize self out bits
      ⦃ (r : Slice U8) => ∃ h : r.length = L.val * (32 * n),
          sliceToBytes r (L.val * (32 * n)) h = Spec.Kopis.PolyVector.serialize n (toVecN n self) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.serialize
  simp only [consts.RING_DEG]
  have hm : 0 < 32 * n := by omega
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (show L.val * (1#usize).val ≤ Usize.max from by
    simpa using le_trans (Nat.le_mul_of_pos_right _ hm) (hlen ▸ out.property))
  have hiv : i.val = L.val := by rw [hi]; simp
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (show i.val * bits.val ≤ Usize.max from by
    rw [hiv, hn]; exact le_trans (Nat.le_mul_of_pos_right _ (by norm_num)) hfit)
  have hi1v : i1.val = L.val * n := by rw [hi1, hiv, hn]
  let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (show i1.val * (256#usize).val ≤ Usize.max from by
    rw [hi1v]; exact hfit)
  have hi2v : i2.val = L.val * n * 256 := by rw [hi2, hi1v]
  let* ⟨ right_val, hrv ⟩ ← Std.Usize.div_spec
  have hrvv : right_val.val = L.val * (32 * n) := by
    rw [hrv, hi2v,
      show L.val * n * 256 = L.val * (32 * n) * 8 from by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  have hmeq : Slice.len out = right_val :=
    UScalar.eq_of_val_eq (by rw [Slice.len_val, hrvv]; exact hlen)
  rw [show massert (Slice.len out = right_val) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
  let* ⟨ i3, hi3 ⟩ ← Std.Usize.mul_spec (show bits.val * (256#usize).val ≤ Usize.max from by
    rw [hn, show (256#usize).val = 256 from rfl]
    have h1 : n * 256 ≤ 13 * 256 := by omega
    have h2 : (13 * 256 : ℕ) ≤ Usize.max := by
      rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega
    omega)
  have hi3v : i3.val = n * 256 := by rw [hi3, hn]
  let* ⟨ chunk_len, hcl ⟩ ← Std.Usize.div_spec
  have hcv : chunk_len.val = 32 * n := by rw [hcl, hi3v]; omega
  apply WP.spec_mono
    (serialize_col_outer_spec { start := 0#usize, «end» := L } self out bits chunk_len n
      hn hrng hcv hlen (by simp) rfl)
  intro r hr
  obtain ⟨hrlen, hrbytes⟩ := hr
  refine ⟨hrlen, ?_⟩
  apply Vector.ext
  intro q hq
  have hcond : ({ start := 0#usize, «end» := L } : core.ops.range.Range Usize).start.val ≤ q / (32 * n) :=
    Nat.zero_le _
  have hmod2 : q % (32 * n) < 32 * n := Nat.mod_lt q hm
  rw [sliceToBytes_getElem! r (L.val * (32 * n)) hrlen q hq, hrbytes q hq,
    if_pos hcond, getElem!_pos (Spec.Kopis.serialize n (toPolyN n ((self.val[q / (32 * n)]!).val[0]!)))
      (q % (32 * n)) hmod2]
  simp only [Spec.Kopis.PolyVector.serialize]
  rw [Vector.getElem_flatten hq, Vector.getElem_map]
  simp only [toVecN, Vector.getElem_ofFn]

end Kopis.Properties
