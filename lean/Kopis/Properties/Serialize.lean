/-
  # Kopis/Properties/Serialize.lean — `deserialize` / `from_bytes` correspondence.

  Proves the Aeneas-extracted `ser::deserialize` (via `RingElem::from_bytes`)
  computes the audited `Spec.Kopis.deserialize`.

  `ser::deserialize` is a sliding-window bit-unpacker: it maintains a `u32`
  `window` holding `bits_in_window` pending bits (LSB-aligned), refills one byte
  at a time until it has ≥ `bits_per_elem` bits, then emits the low
  `bits_per_elem` bits of the window as one coefficient and shifts them out.
  This mirrors MLKEM's verified `decode` bit-pump (`Encoding/DecompressInner`).
-/
import ExtractedRust
import Spec.Kopis.Spec

open Aeneas Aeneas.Std Result
open RustKopisSerial
open Spec (𝔹 bytesToBits)

namespace Kopis.Properties

open arithmetic.ring_arith (RingElem)

/-! ## Bridges -/

/-- Interpret a Rust `Slice U8` of length `n` as a spec `𝔹 n`. -/
def sliceToBytes (s : Slice U8) (n : ℕ) (h : s.length = n) : 𝔹 n :=
  Vector.ofFn fun (i : Fin n) => (s.val[i.val]'(by have := i.isLt; simp only [Slice.length] at h; omega)).bv

/-- `sliceToBytes` in list form: the underlying `U8` slice mapped to bit-vectors. -/
theorem sliceToBytes_toList {s : Slice U8} {n : ℕ} (h : s.length = n) :
    (sliceToBytes s n h).toList = s.val.map (·.bv) := by
  apply List.ext_getElem
  · simp only [sliceToBytes, Vector.toList_length, List.length_map]
    simp only [Slice.length] at h; omega
  · intro k h1 h2
    simp only [sliceToBytes, Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_map]

/-- Interpret a Rust `RingElem` as a spec ring element over `ZMod (2¹³)` (the
modulus `deserialize 13` targets; each decoded coefficient is `< 2¹³`). -/
def toRingElem13 (a : RingElem) : Spec.Kopis.Polynomial (2 ^ 13) :=
  Vector.ofFn fun (i : Fin 256) =>
    ((a.val[i.val]'(by have := a.property; grind)).val : ZMod (2 ^ 13))

/-! ## Bit-stream helpers

The decoder reads a little-endian bit stream: bit `m` is bit `m % 8` of byte
`m / 8`.  `streamNat lo len` is the value of the window `[lo, lo+len)` of that
stream, LSB-first. -/

/-- Bit `m` of the little-endian byte stream (`0`/`1`). -/
def streamBit (bytes : Slice U8) (m : ℕ) : ℕ :=
  ((bytes.val[m / 8]!).val.testBit (m % 8)).toNat

/-- Value of stream bits `[lo, lo+len)`, LSB-first. -/
def streamNat (bytes : Slice U8) (lo len : ℕ) : ℕ :=
  ∑ b ∈ Finset.range len, streamBit bytes (lo + b) * 2 ^ b

@[simp] theorem streamNat_zero (bytes : Slice U8) (lo : ℕ) : streamNat bytes lo 0 = 0 := by
  simp [streamNat]

theorem streamNat_succ (bytes : Slice U8) (lo len : ℕ) :
    streamNat bytes lo (len + 1) = streamNat bytes lo len + streamBit bytes (lo + len) * 2 ^ len := by
  simp [streamNat, Finset.sum_range_succ]

theorem streamBit_le_one (bytes : Slice U8) (m : ℕ) : streamBit bytes m ≤ 1 := by
  unfold streamBit; cases (bytes.val[m / 8]!).val.testBit (m % 8) <;> simp

theorem streamNat_lt (bytes : Slice U8) (lo len : ℕ) : streamNat bytes lo len < 2 ^ len := by
  induction len with
  | zero => simp
  | succ n ih =>
    rw [streamNat_succ, pow_succ]
    have : streamBit bytes (lo + n) * 2 ^ n ≤ 2 ^ n := by
      have := streamBit_le_one bytes (lo + n); nlinarith [Nat.one_le_two_pow (n := n)]
    omega

/-- Splitting a window: `[lo, lo+a+b)` = low `a` bits plus the next `b` bits shifted. -/
theorem streamNat_split (bytes : Slice U8) (lo a b : ℕ) :
    streamNat bytes lo (a + b)
      = streamNat bytes lo a + 2 ^ a * streamNat bytes (lo + a) b := by
  induction b with
  | zero => simp
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 from by ring, streamNat_succ, ih, streamNat_succ,
        show lo + (a + n) = (lo + a) + n from by ring, pow_add]
    ring

/-- Disjoint OR is addition: OR-ing a value `< 2ᵏ` with something shifted up by `k`
adds them (no bit overlap). -/
theorem lor_add_of_lt {w b k : ℕ} (hw : w < 2 ^ k) :
    w ||| (b <<< k) = w + b <<< k := by
  rw [Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro j
  have e1 : (b * 2 ^ k).testBit j = if j < k then false else b.testBit (j - k) := by
    rw [show b * 2 ^ k = 2 ^ k * b + 0 from by ring,
        Nat.testBit_two_pow_mul_add b (by positivity) j]; simp
  have e2 : (w + b * 2 ^ k).testBit j = if j < k then w.testBit j else b.testBit (j - k) := by
    rw [show w + b * 2 ^ k = 2 ^ k * b + w from by ring]
    exact Nat.testBit_two_pow_mul_add b hw j
  rw [Nat.testBit_lor, e1, e2]
  by_cases hjk : j < k
  · simp [hjk]
  · have hwf : w.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hjk)))
    simp [hjk, hwf]

/-- Multiplication form of `lor_add_of_lt`: OR with a value that is a multiple of
`2ᵏ` (and whose low part is `< 2ᵏ`) is addition. -/
theorem lor_mul_of_lt {w b k : ℕ} (hw : w < 2 ^ k) :
    w ||| (b * 2 ^ k) = w + b * 2 ^ k := by
  rw [← Nat.shiftLeft_eq, lor_add_of_lt hw, Nat.shiftLeft_eq]

/-- A natural mod `2ᵏ` is the LSB-first sum of its bottom `k` bits. -/
theorem sum_testBit_eq_mod (n k : ℕ) :
    ∑ i ∈ Finset.range k, (n.testBit i).toNat * 2 ^ i = n % 2 ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]
    have h : (n.testBit m).toNat = n / 2 ^ m % 2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ m) with h | h <;> simp [h]
    rw [h]; ring

/-- One byte equals its 8 stream bits (byte `bp` covers stream positions `[8·bp, 8·bp+8)`). -/
theorem streamNat_byte (bytes : Slice U8) (bp : ℕ) :
    streamNat bytes (8 * bp) 8 = (bytes.val[bp]!).val := by
  have hb : (bytes.val[bp]!).val < 256 := by scalar_tac
  unfold streamNat
  rw [show (∑ c ∈ Finset.range 8, streamBit bytes (8 * bp + c) * 2 ^ c)
        = ∑ c ∈ Finset.range 8, ((bytes.val[bp]!).val.testBit c).toNat * 2 ^ c from ?_]
  · rw [sum_testBit_eq_mod, show (2:ℕ) ^ 8 = 256 from by norm_num, Nat.mod_eq_of_lt hb]
  · apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.mem_range] at hc
    unfold streamBit
    rw [show (8 * bp + c) / 8 = bp from by omega, show (8 * bp + c) % 8 = c from by omega]

/-! ## `deserialize` / `from_bytes` correspondence -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- **Refill-loop spec.**  `deserialize_loop0_loop0` reads whole bytes into the
`window` until it holds ≥ 13 bits.  Invariant: the window's value is exactly the
stream bits `[lo, lo + bits_in_window)`, and `8·byte_pos = lo + bits_in_window`. -/
theorem deserialize_refill_spec (bytes : Slice U8) (window : U32) (biw bp : Usize) (lo : ℕ)
    (hbiw20 : biw.val ≤ 20)
    (hlo : 8 * bp.val = lo + biw.val)
    (hwin : window.val = streamNat bytes lo biw.val)
    (hbytes : lo + 13 ≤ 8 * bytes.length) :
    ser.deserialize_generic_loop0_loop0 bytes 13#usize window biw bp
      ⦃ (r : U32 × Usize × Usize) =>
          13 ≤ r.2.1.val ∧ r.2.1.val ≤ 20 ∧ 8 * r.2.2.val = lo + r.2.1.val ∧
          r.1.val = streamNat bytes lo r.2.1.val ⦄ := by
  unfold ser.deserialize_generic_loop0_loop0
  by_cases hlt : biw < 13#usize
  · rw [if_pos hlt]
    have hlt' : biw.val < 13 := by scalar_tac
    have hbp : bp.val < bytes.length := by scalar_tac
    have hwlt : window.val < 2 ^ biw.val := hwin ▸ streamNat_lt bytes lo biw.val
    let* ⟨ i, hi ⟩ ← Slice.index_usize_spec
    have hi_lt : i.val < 256 := by rw [hi]; scalar_tac
    let* ⟨ i1, hi1 ⟩ ← UScalar.cast_inBounds_spec
    let* ⟨ i2, hi2, hi2bv ⟩ ← Std.U32.ShiftLeft_spec
    have hi1_lt : i1.val < 256 := by rw [hi1]; exact hi_lt
    have hbound : i1.val * 2 ^ biw.val < 2 ^ 32 := by
      calc i1.val * 2 ^ biw.val ≤ 255 * 2 ^ 12 :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ < 2 ^ 32 := by norm_num
    have hsz : Std.U32.size = 2 ^ 32 := by simp [Std.U32.size, Std.U32.numBits]
    have hi2' : i2.val = i1.val * 2 ^ biw.val := by
      rw [hi2, Nat.shiftLeft_eq]
      apply Nat.mod_eq_of_lt
      rw [hsz]; exact hbound
    have hbyte : (bytes.val[bp.val]!).val = i1.val := by
      rw [getElem!_pos bytes.val bp.val hbp, hi1, hi]
    simp only [lift, bind_tc_ok]
    let* ⟨ bp1, hbp1 ⟩ ← Std.Usize.add_spec
    let* ⟨ biw1, hbiw1 ⟩ ← Std.Usize.add_spec
    have hbiw1' : biw1.val = biw.val + 8 := by scalar_tac
    have hlo' : 8 * bp1.val = lo + biw1.val := by scalar_tac
    have hwin' : (window ||| i2).val = streamNat bytes lo biw1.val := by
      rw [hbiw1', UScalar.val_or, hi2',
        show i1.val * 2 ^ biw.val = i1.val <<< biw.val from by rw [Nat.shiftLeft_eq],
        lor_add_of_lt hwlt, Nat.shiftLeft_eq, hwin, streamNat_split]
      congr 1
      rw [show lo + biw.val = 8 * bp.val from hlo.symm, streamNat_byte, hbyte]
      ring
    exact deserialize_refill_spec bytes (window ||| i2) biw1 bp1 lo (by omega) hlo' hwin' hbytes
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    exact ⟨by scalar_tac, hbiw20, hlo, hwin⟩
termination_by 13 - biw.val
decreasing_by scalar_tac

/-- **Outer-loop spec.**  Processing indices `[iter.start, 256)` writes coefficient
`j = streamNat (13·j) 13` into each output slot; the window enters slot `k` holding
the stream bits `[13·k, 13·k + bits_in_window)`. -/
theorem deserialize_outer_spec {N : Usize} (hN : N.val = 256)
    (iter : core.ops.range.Range Usize) (bytes : Slice U8) (out : Array U16 N)
    (bitmask window : U32) (biw bp : Usize)
    (hmask : bitmask.val = 2 ^ 13 - 1)
    (hstart : iter.start.val ≤ 256) (hend : iter.«end».val = 256)
    (hbiwlt : biw.val < 13)
    (hlo : 8 * bp.val = 13 * iter.start.val + biw.val)
    (hwin : window.val = streamNat bytes (13 * iter.start.val) biw.val)
    (hbytes : 13 * 256 ≤ 8 * bytes.length) :
    ser.deserialize_generic_loop0 iter bytes 13#usize out bitmask window biw bp
      ⦃ (r : Array U16 N) =>
          ∀ j (hj : j < 256),
            (r.val[j]'(by have := r.property; grind)).val
              = if j < iter.start.val then (out.val[j]'(by have := out.property; grind)).val
                else streamNat bytes (13 * j) 13 ⦄ := by
  unfold ser.deserialize_generic_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hk_lt : iter.start.val < 256 := by scalar_tac
    -- refill
    let* ⟨ window1, biw1, bp1, hbiw1, hbiw1ub, hlo1, hwin1 ⟩ ←
      deserialize_refill_spec bytes window biw bp (13 * iter.start.val) (by omega) hlo hwin (by omega)
    -- extract element = low 13 bits
    have hsplit : streamNat bytes (13 * iter.start.val) biw1.val
        = streamNat bytes (13 * iter.start.val) 13
          + 2 ^ 13 * streamNat bytes (13 * iter.start.val + 13) (biw1.val - 13) := by
      conv_lhs => rw [show biw1.val = 13 + (biw1.val - 13) from by omega]
      rw [streamNat_split]
    have helem_lt : streamNat bytes (13 * iter.start.val) 13 < 2 ^ 13 := streamNat_lt _ _ _
    rw [show (lift (window1 &&& bitmask) : Result U32) = ok (window1 &&& bitmask) from rfl, bind_tc_ok]
    have hi_val : (window1 &&& bitmask).val = streamNat bytes (13 * iter.start.val) 13 := by
      rw [UScalar.val_and, hmask, Nat.and_two_pow_sub_one_eq_mod, hwin1, hsplit,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt helem_lt]
    have hi1bound : (window1 &&& bitmask).val ≤ UScalar.max .U16 := by
      have h13 : (2:ℕ) ^ 13 = 8192 := by norm_num
      rw [hi_val]; simp only [UScalar.max_UScalarTy_U16_eq, U16.max_eq]
      have := helem_lt; omega
    let* ⟨ i1, hi1 ⟩ ← UScalar.cast_inBounds_spec .U16 (window1 &&& bitmask) hi1bound
    have hi1_val : i1.val = streamNat bytes (13 * iter.start.val) 13 := by rw [hi1, hi_val]
    let* ⟨ a, ha ⟩ ← Array.update_spec
    let* ⟨ window2, hw2, hw2bv ⟩ ← Std.U32.ShiftRight_spec
    let* ⟨ biw2, hbiw2 ⟩ ← Std.Usize.sub_spec
    have hbiw2' : biw2.val = biw1.val - 13 := by scalar_tac
    have hw2' : window2.val = streamNat bytes (13 * iter1.start.val) biw2.val := by
      rw [hstart', show 13 * (iter.start.val + 1) = 13 * iter.start.val + 13 from by ring,
        hw2, hwin1, hsplit, hbiw2', Nat.shiftRight_eq_div_pow,
        Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ 13), Nat.div_eq_of_lt helem_lt,
        Nat.zero_add]
    have hlo' : 8 * bp1.val = 13 * iter1.start.val + biw2.val := by
      rw [hstart', hbiw2']; omega
    have hbiw2lt : biw2.val < 13 := by omega
    -- recurse
    apply WP.spec_mono
      (deserialize_outer_spec hN iter1 bytes a bitmask window2 biw2 bp1 hmask
        (by rw [hstart']; scalar_tac) (by rw [hend']; exact hend) hbiw2lt hlo' hw2' hbytes)
    intro r hr j hj
    have ihj := hr j hj
    rw [hstart'] at ihj
    by_cases hjk : j < iter.start.val
    · rw [if_pos hjk, ihj, if_pos (by omega)]
      rw [ha]; simp only [Array.set_val_eq]
      rw [List.getElem_set_ne (by omega)]
    · rw [if_neg hjk]
      by_cases hjeq : j = iter.start.val
      · subst hjeq
        rw [ihj, if_pos (by omega), ha]
        simp only [Array.set_val_eq, List.getElem_set_self, hi1_val]
      · rw [ihj, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro j hj
    rw [if_pos (by scalar_tac)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## Spec-side: evaluating the `deserialize` `Id.run` loop -/

/-- Indexed-invariant evaluator for an `Id.run` `forIn'` loop over a `Vector`
(generic; replicated locally to keep Kopis independent of the MLKEM modules). -/
private theorem forIn'_getElem_indexed {α : Type} {β : Type} {m : Nat} :
    ∀ (xs : List α) (init : Vector β m)
    (body : (a : α) → a ∈ xs → Vector β m → Id (ForInStep (Vector β m)))
    (i : Nat) (hi : i < m) (val : β)
    (P : Nat → Vector β m → Prop)
    (hInit : P 0 init)
    (hFinal : ∀ dw, P xs.length dw → dw[i] = val)
    (_hStep : ∀ (k : Nat) (hk : k < xs.length) b, P k b →
      ∀ a (ha : a ∈ xs), a = xs[k]'hk →
      ∃ b', body a ha b = pure (ForInStep.yield b') ∧ P (k + 1) b'),
    (Id.run (forIn' xs init body))[i] = val := by
  intro xs; induction xs with
  | nil => intro init body i hi val P hInit hFinal _hStep; exact hFinal init hInit
  | cons x xs ih =>
    intro init body i hi val P hInit hFinal hStep
    simp only [List.forIn'_cons, Id.run, Bind.bind]
    obtain ⟨b', hb'_eq, hb'_P⟩ := hStep 0 (Nat.zero_lt_succ _) init hInit x (.head _) rfl
    conv_lhs => arg 1; rw [hb'_eq]
    exact ih b' (fun a' mm b => body a' (.tail _ mm) b) i hi val (fun k => P (k + 1))
      hb'_P
      (fun dw hP => hFinal dw (by rwa [List.length_cons]))
      (fun k hk b hPk a ha heq => by
        have hk' : k + 1 < (x :: xs).length := by simp; omega
        exact hStep (k + 1) hk' b hPk a (.tail _ ha) (by simp [heq]))

/-- Bit index bound (same statement as the spec's private `serialize_idx_lt`). -/
private theorem deser_idx_lt {n i j : ℕ} (hi : i < 256) (hj : j < n) :
    n * i + j < 8 * (32 * n) := by
  calc n * i + j < n * i + n := by omega
    _ = n * (i + 1) := by ring
    _ ≤ n * 256 := Nat.mul_le_mul_left n (by omega)
    _ = 8 * (32 * n) := by ring

/-- The `i`-th coefficient of the spec `deserialize` is exactly its loop body. -/
theorem deserialize_get (n : ℕ) (B : 𝔹 (32 * n)) (i : ℕ) (hi : i < 256) :
    (Spec.Kopis.deserialize n B)[i]'hi
      = ∑ j : Fin n, ((bytesToBits B)[n * i + j.val]'(deser_idx_lt hi j.isLt)).toNat * 2 ^ j.val := by
  unfold Spec.Kopis.deserialize
  simp only [Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  refine forIn'_getElem_indexed (List.range' 0 256) _ _ i hi _
    (P := fun s (F' : Spec.Kopis.Polynomial (2 ^ n)) =>
      (F'[i]'hi) = if s ≤ i then (0 : ZMod (2 ^ n))
        else ((∑ j : Fin n, ((bytesToBits B)[n * i + j.val]'(deser_idx_lt hi j.isLt)).toNat
                * 2 ^ j.val : ℕ) : ZMod (2 ^ n)))
    ?hInit ?hFinal ?hStep
  case hInit =>
    show (Spec.Kopis.Polynomial.zero (2 ^ n))[i]'hi = _
    simp [Spec.Kopis.Polynomial.zero, Vector.getElem_replicate]
  case hFinal =>
    intro dw hP
    rw [show (List.range' 0 256).length = 256 from by simp, if_neg (by omega)] at hP
    exact hP
  case hStep =>
    intro k hk F' hPF' a ha ha_eq
    have hk_lt : k < 256 := (show (List.range' 0 256).length = 256 from by simp) ▸ hk
    have ha_val : a = k := by rw [ha_eq]; simp [List.getElem_range']
    have ha_lt : a < 256 := ha_val ▸ hk_lt
    refine ⟨_, rfl, ?_⟩
    rw [Vector.getElem_set ha_lt hi]
    by_cases h_eq : a = i
    · rw [if_pos h_eq, if_neg (by omega : ¬ k + 1 ≤ i)]
      simp only [h_eq]
      push_cast
      rfl
    · rw [if_neg h_eq, hPF']
      have hki : k ≠ i := by rw [← ha_val]; exact h_eq
      by_cases hle : k ≤ i <;> [rw [if_pos hle, if_pos (by omega)]; rw [if_neg hle, if_neg (by omega)]]

/-- The bridged spec bit stream `bytesToBits (sliceToBytes …)` agrees with `streamBit`. -/
theorem streamBit_eq_bit (bytes : Slice U8) (n m : ℕ) (h : bytes.length = 32 * n)
    (hm : m < 8 * (32 * n)) :
    ((bytesToBits (sliceToBytes bytes (32 * n) h))[m]'(by simpa using hm)).toNat = streamBit bytes m := by
  have hm8 : m / 8 < 32 * n := by omega
  unfold streamBit
  simp only [bytesToBits, sliceToBytes, Vector.getElem_ofFn]
  rw [getElem!_pos bytes.val (m / 8) (by simp only [Slice.length] at h ⊢; omega)]
  rfl

/-- `streamNat (n·j) n` equals the spec's per-coefficient `Fin`-sum over the bridged bits. -/
private theorem streamNat_eq_sum (bytes : Slice U8) (n j : ℕ) (h : bytes.length = 32 * n) (hj : j < 256) :
    streamNat bytes (n * j) n
      = ∑ k : Fin n, ((bytesToBits (sliceToBytes bytes (32 * n) h))[n * j + k.val]'(deser_idx_lt hj k.isLt)).toNat
          * 2 ^ k.val := by
  unfold streamNat
  rw [← Fin.sum_univ_eq_sum_range (fun b => streamBit bytes (n * j + b) * 2 ^ b) n]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact (streamBit_eq_bit bytes n (n * j + k.val) h (deser_idx_lt hj k.isLt)).symm

/-! ## `deserialize_13` — the branchless fixed-shift fast path

  `RingElem::deserialize` now dispatches on `bits_per_elem`: at 13 bits (matrix /
  public-key expansion, the hot width) it calls `ser::deserialize_13`, which unpacks
  each aligned 13-byte group into 8 coefficients with fixed shifts and masks (no
  sliding window).  We prove that path computes the same `streamNat` coefficients as
  the audited generic decoder, and reuse the spec bridge below. -/

/-- The closure `|k| b[k] as u16` reads byte `k` of the group and widens it to `u16`. -/
private theorem deser13_closure_spec (b : Slice U8) (k : Usize) (hk : k.val < b.length) :
    ser.deserialize_13.closure.Insts.CoreOpsFunctionFnTupleUsizeU16.call b k
      ⦃ (r : U16) => r.val = (b.val[k.val]'(by simp only [Slice.length] at hk; omega)).val ⦄ := by
  unfold ser.deserialize_13.closure.Insts.CoreOpsFunctionFnTupleUsizeU16.call
  let* ⟨ i, hi ⟩ ← Slice.index_usize_spec
  rw [U8.cast_U16_val_eq, hi]

/-- Three-byte window lemma: a 13-bit little-endian window starting at bit `8·B + r`
(with `r ≤ 7`) is `(v₀ + 2⁸·v₁ + 2¹⁶·v₂) >> r`, masked to 13 bits, where `vᵢ = bytes[B+i]`. -/
private theorem streamNat_window (bytes : Slice U8) (B r : ℕ) (hr : r ≤ 7) :
    streamNat bytes (8 * B + r) 13
      = ((bytes.val[B]!).val + 2 ^ 8 * (bytes.val[B+1]!).val + 2 ^ 16 * (bytes.val[B+2]!).val)
          / 2 ^ r % 2 ^ 13 := by
  -- The 3-byte value equals the 24-bit stream window at `8·B`.
  have hW : streamNat bytes (8 * B) 24
      = (bytes.val[B]!).val + 2 ^ 8 * (bytes.val[B+1]!).val + 2 ^ 16 * (bytes.val[B+2]!).val := by
    rw [show (24 : ℕ) = 8 + 16 from rfl, streamNat_split, show (16 : ℕ) = 8 + 8 from rfl,
        streamNat_split, streamNat_byte, show 8 * B + 8 = 8 * (B + 1) from by ring,
        streamNat_byte, show 8 * (B + 1) + 8 = 8 * (B + 2) from by ring, streamNat_byte]
    ring
  -- Peel `[8B, 8B+r)` and `[8B+r, 8B+r+13)` off the 24-bit window.
  have hsplit1 : streamNat bytes (8 * B) 24
      = streamNat bytes (8 * B) r + 2 ^ r * streamNat bytes (8 * B + r) (24 - r) := by
    have := streamNat_split bytes (8 * B) r (24 - r)
    rwa [show r + (24 - r) = 24 from by omega] at this
  have hsplit2 : streamNat bytes (8 * B + r) (24 - r)
      = streamNat bytes (8 * B + r) 13 + 2 ^ 13 * streamNat bytes (8 * B + r + 13) (24 - r - 13) := by
    have := streamNat_split bytes (8 * B + r) 13 (24 - r - 13)
    rwa [show (13 : ℕ) + (24 - r - 13) = 24 - r from by omega] at this
  set A := streamNat bytes (8 * B) r with hA_def
  set C := streamNat bytes (8 * B + r) 13 with hC_def
  set D := streamNat bytes (8 * B + r + 13) (24 - r - 13) with hD_def
  have hAlt : A < 2 ^ r := streamNat_lt _ _ _
  have hClt : C < 2 ^ 13 := streamNat_lt _ _ _
  have hWACD : (bytes.val[B]!).val + 2 ^ 8 * (bytes.val[B+1]!).val + 2 ^ 16 * (bytes.val[B+2]!).val
      = A + 2 ^ r * (C + 2 ^ 13 * D) := by rw [← hW, hsplit1, hsplit2]
  rw [hWACD, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ r),
      Nat.div_eq_of_lt hAlt, Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hClt]

/-
  ROADMAP for the three sorries below (self-contained; see `deserialize_outer_spec`
  above for the analogous *generic*-decoder proof to mirror).

  Useful extracted defs live in `ExtractedRust.lean`: `ser.deserialize_13`,
  `ser.deserialize_13_loop`, `...closure...call`, `arithmetic.ring_arith.RingElem.deserialize`.

  Confirmed library lemma names:
    * `U8.cast_U16_val_eq  : (UScalar.cast .U16 x).val = x.val`   (Aeneas/Std/Scalar/Casts.lean)
    * `UScalar.ShiftLeft_spec` / `UScalar.ShiftRight_spec`, and the `@[step]`-tagged
      per-type versions (Aeneas/Std/Scalar/Bitwise.lean) — usable via `let*`/`step`.
    * `UScalar.val_and`, `Nat.and_two_pow_sub_one_eq_mod`, `lor_add_of_lt` (local),
      `UScalar.cast_inBounds_spec` — all already used in `deserialize_outer_spec`.
    * `core.array.TryFromSharedArraySlice.try_from N s = if s.len = N then .Ok ⟨s.val,_⟩ …`
      (Aeneas/Std/Array/ArraySlice.lean:314) — for `from_bytes_spec`'s plumbing.

  (1) deser13_closure_spec: unfold the closure; `let* ⟨i,hi⟩ ← Slice.index_usize_spec`;
      `simp only [WP.spec_ok]`; close with `U8.cast_U16_val_eq` + `hi`.

  (2) deserialize_13_spec: prove `deserialize_13_loop` by a group loop-invariant like
      `deserialize_outer_spec`. Helper "window lemma" (generic in r, no omega needed):
        streamNat bytes (8*B + r) 13 = ((v0 + 2^8*v1 + 2^16*v2) / 2^r) % 2^13,  vi = bytes[B+i]
      via streamNat_split (8+8+8 for the 3-byte value; then a=r; then a=13) + streamNat_lt
      + Nat.add_mul_div_left / Nat.div_eq_of_lt (exactly the `window2` step in
      deserialize_outer_spec). Per group g, coeff index j = 8g+t has bit offset
      13*j = 8*(13g + off_t) + r_t with:
          t:      0   1   2   3   4   5   6   7
          off_t:  0   1   3   4   6   8   9   11
          r_t:    0   5   2   7   4   1   6   3
      Rewrite streamNat via the window lemma (concrete r_t), express the extracted U16
      `<<< &&& |||` chain as Nat via the shift/and/`lor_add_of_lt` lemmas + `deser13_closure_spec`
      (keeping each intermediate < 2^13 < 2^16 so no U16 wrap), then `omega` (r_t concrete →
      2^r_t, 2^13 are literals; feed byte bounds `< 256`). Sub-slice fact: for
      `b = bytes[13g .. 13g+13]`, `b.val[k]! = bytes.val[13g+k]!` (range-index; check
      `core.slice.index.SliceIndexRangeUsizeSlice`). Bridge `arr.val = bytes.val` at the end.

  (3) from_bytes_spec: unfold `RingElem.deserialize`; `simp only [consts.RING_DEG,
      consts.MODULUS_Q_BITS, consts.MODULUS_P_BITS]`; step scalar mul/div; discharge the
      `massert` (both sides = 416 from `hlen`); take the `13 = 13` branch; resolve
      `try_from 416`/`unwrap` (lengths match ⇒ array with `.val = bytes.val`); then
      `apply WP.spec_bind (deserialize_13_spec bytes arr <arr.val=bytes.val> hlen416)`
      and finish with the SAME bridge as the old proof:
        intro r hr; simp only [WP.spec_ok]; apply Vector.ext; intro jj hjj
        simp only [toRingElem13, Vector.getElem_ofFn]
        rw [deserialize_get 13 (sliceToBytes bytes (32*13) hlen) jj hjj]
        have hval := hr jj hjj
        rw [hval, streamNat_eq_sum bytes 13 jj hlen hjj]
      (No `if_neg` needed — `deserialize_13_spec`'s `hr` has no `if`.)
-/

/-! Per-coefficient extraction lemmas (one per output slot in a 13-byte group).  Each
matches the branchless shift/mask/OR the Rust extractor computes against the audited
little-endian 13-bit window `(vA + 2⁸·vB + 2¹⁶·vC) >> r`, masked to 13 bits.  Stated
over abstract `U16`s and byte values so the arithmetic is discharged by `omega` in a
clean context (the loop body itself is far too hypothesis-heavy for `omega`). -/

private theorem coef0 (i2 i3 i4 i5 i6 : U16) (v0 v1 v2 : ℕ)
    (e2 : i2.val = v0) (e3 : i3.val = v1) (e4 : i4.val = (i3 &&& 31#u16).val)
    (e5 : i5.val = i4.val <<< 8 % U16.size) (e6 : i6.val = (i2 ||| i5).val)
    (_b0 : v0 < 256) (_b1 : v1 < 256) (_b2 : v2 < 256) :
    i6.val = (v0 + (2 ^ 8 * v1 + 2 ^ 16 * v2)) / 2 ^ 0 % 2 ^ 13 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have h4 : i4.val = v1 % 2 ^ 5 := by
    rw [e4, UScalar.val_and, e3, show ((31#u16).val : ℕ) = 2 ^ 5 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have h5 : i5.val = v1 % 2 ^ 5 * 2 ^ 8 := by
    rw [e5, h4, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  rw [e6, UScalar.val_or, e2, h5, lor_mul_of_lt (show v0 < 2 ^ 8 by omega)]; omega

private theorem coef1 (i3 i7 i8 i9 i10 i11 i12 i13 i15 : U16) (v1 v2 v3 : ℕ)
    (e3 : i3.val = v1) (h7 : i7.val = i3.val >>> 5) (e8 : i8.val = v2)
    (h9 : i9.val = i8.val <<< 3 % U16.size) (h10 : i10.val = (i7 ||| i9).val)
    (e11 : i11.val = v3) (h12 : i12.val = (i11 &&& 3#u16).val)
    (h13 : i13.val = i12.val <<< 11 % U16.size) (h15 : i15.val = (i10 ||| i13).val)
    (_b1 : v1 < 256) (_b2 : v2 < 256) (_b3 : v3 < 256) :
    i15.val = (v1 + (2 ^ 8 * v2 + 2 ^ 16 * v3)) / 2 ^ 5 % 2 ^ 13 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have p7 : i7.val = v1 / 2 ^ 5 := by rw [h7, e3, Nat.shiftRight_eq_div_pow]
  have p9 : i9.val = v2 * 2 ^ 3 := by
    rw [h9, e8, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  have p12 : i12.val = v3 % 2 ^ 2 := by
    rw [h12, UScalar.val_and, e11, show ((3#u16).val : ℕ) = 2 ^ 2 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have p13 : i13.val = v3 % 2 ^ 2 * 2 ^ 11 := by
    rw [h13, p12, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  have p10 : i10.val = v1 / 2 ^ 5 + v2 * 2 ^ 3 := by
    rw [h10, UScalar.val_or, p7, p9, lor_mul_of_lt (show v1 / 2 ^ 5 < 2 ^ 3 by omega)]
  rw [h15, UScalar.val_or, p10, p13, lor_mul_of_lt (show v1 / 2 ^ 5 + v2 * 2 ^ 3 < 2 ^ 11 by omega)]
  omega

private theorem coef2 (i11 i16 i17 i18 i19 i21 : U16) (v3 v4 v5 : ℕ)
    (e11 : i11.val = v3) (h16 : i16.val = i11.val >>> 2) (e17 : i17.val = v4)
    (h18 : i18.val = (i17 &&& 127#u16).val) (h19 : i19.val = i18.val <<< 6 % U16.size)
    (h21 : i21.val = (i16 ||| i19).val) (_b3 : v3 < 256) (_b4 : v4 < 256) (_b5 : v5 < 256) :
    i21.val = (v3 + (2 ^ 8 * v4 + 2 ^ 16 * v5)) / 2 ^ 2 % 2 ^ 13 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have p16 : i16.val = v3 / 2 ^ 2 := by rw [h16, e11, Nat.shiftRight_eq_div_pow]
  have p18 : i18.val = v4 % 2 ^ 7 := by
    rw [h18, UScalar.val_and, e17, show ((127#u16).val : ℕ) = 2 ^ 7 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have p19 : i19.val = v4 % 2 ^ 7 * 2 ^ 6 := by
    rw [h19, p18, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  rw [h21, UScalar.val_or, p16, p19, lor_mul_of_lt (show v3 / 2 ^ 2 < 2 ^ 6 by omega)]; omega

private theorem coef3 (i17 i22 i23 i24 i25 i26 i27 i28 i30 : U16) (v4 v5 v6 : ℕ)
    (e17 : i17.val = v4) (h22 : i22.val = i17.val >>> 7) (e23 : i23.val = v5)
    (h24 : i24.val = i23.val <<< 1 % U16.size) (h25 : i25.val = (i22 ||| i24).val)
    (e26 : i26.val = v6) (h27 : i27.val = (i26 &&& 15#u16).val)
    (h28 : i28.val = i27.val <<< 9 % U16.size) (h30 : i30.val = (i25 ||| i28).val)
    (_b4 : v4 < 256) (_b5 : v5 < 256) (_b6 : v6 < 256) :
    i30.val = (v4 + (2 ^ 8 * v5 + 2 ^ 16 * v6)) / 2 ^ 7 % 2 ^ 13 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have p22 : i22.val = v4 / 2 ^ 7 := by rw [h22, e17, Nat.shiftRight_eq_div_pow]
  have p24 : i24.val = v5 * 2 ^ 1 := by
    rw [h24, e23, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  have p27 : i27.val = v6 % 2 ^ 4 := by
    rw [h27, UScalar.val_and, e26, show ((15#u16).val : ℕ) = 2 ^ 4 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have p28 : i28.val = v6 % 2 ^ 4 * 2 ^ 9 := by
    rw [h28, p27, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  have p25 : i25.val = v4 / 2 ^ 7 + v5 * 2 ^ 1 := by
    rw [h25, UScalar.val_or, p22, p24, lor_mul_of_lt (show v4 / 2 ^ 7 < 2 ^ 1 by omega)]
  rw [h30, UScalar.val_or, p25, p28, lor_mul_of_lt (show v4 / 2 ^ 7 + v5 * 2 ^ 1 < 2 ^ 9 by omega)]
  omega

private theorem coef4 (i26 i31 i32 i33 i34 i35 i36 i37 i39 : U16) (v6 v7 v8 : ℕ)
    (e26 : i26.val = v6) (h31 : i31.val = i26.val >>> 4) (e32 : i32.val = v7)
    (h33 : i33.val = i32.val <<< 4 % U16.size) (h34 : i34.val = (i31 ||| i33).val)
    (e35 : i35.val = v8) (h36 : i36.val = (i35 &&& 1#u16).val)
    (h37 : i37.val = i36.val <<< 12 % U16.size) (h39 : i39.val = (i34 ||| i37).val)
    (_b6 : v6 < 256) (_b7 : v7 < 256) (_b8 : v8 < 256) :
    i39.val = (v6 + (2 ^ 8 * v7 + 2 ^ 16 * v8)) / 2 ^ 4 % 2 ^ 13 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have p31 : i31.val = v6 / 2 ^ 4 := by rw [h31, e26, Nat.shiftRight_eq_div_pow]
  have p33 : i33.val = v7 * 2 ^ 4 := by
    rw [h33, e32, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  have p36 : i36.val = v8 % 2 ^ 1 := by
    rw [h36, UScalar.val_and, e35, show ((1#u16).val : ℕ) = 2 ^ 1 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have p37 : i37.val = v8 % 2 ^ 1 * 2 ^ 12 := by
    rw [h37, p36, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  have p34 : i34.val = v6 / 2 ^ 4 + v7 * 2 ^ 4 := by
    rw [h34, UScalar.val_or, p31, p33, lor_mul_of_lt (show v6 / 2 ^ 4 < 2 ^ 4 by omega)]
  rw [h39, UScalar.val_or, p34, p37, lor_mul_of_lt (show v6 / 2 ^ 4 + v7 * 2 ^ 4 < 2 ^ 12 by omega)]
  omega

private theorem coef5 (i35 i40 i41 i42 i43 i45 : U16) (v8 v9 v10 : ℕ)
    (e35 : i35.val = v8) (h40 : i40.val = i35.val >>> 1) (e41 : i41.val = v9)
    (h42 : i42.val = (i41 &&& 63#u16).val) (h43 : i43.val = i42.val <<< 7 % U16.size)
    (h45 : i45.val = (i40 ||| i43).val) (_b8 : v8 < 256) (_b9 : v9 < 256) (_b10 : v10 < 256) :
    i45.val = (v8 + (2 ^ 8 * v9 + 2 ^ 16 * v10)) / 2 ^ 1 % 2 ^ 13 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have p40 : i40.val = v8 / 2 ^ 1 := by rw [h40, e35, Nat.shiftRight_eq_div_pow]
  have p42 : i42.val = v9 % 2 ^ 6 := by
    rw [h42, UScalar.val_and, e41, show ((63#u16).val : ℕ) = 2 ^ 6 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have p43 : i43.val = v9 % 2 ^ 6 * 2 ^ 7 := by
    rw [h43, p42, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  rw [h45, UScalar.val_or, p40, p43, lor_mul_of_lt (show v8 / 2 ^ 1 < 2 ^ 7 by omega)]; omega

private theorem coef6 (i41 i46 i47 i48 i49 i50 i51 i52 i54 : U16) (v9 v10 v11 : ℕ)
    (e41 : i41.val = v9) (h46 : i46.val = i41.val >>> 6) (e47 : i47.val = v10)
    (h48 : i48.val = i47.val <<< 2 % U16.size) (h49 : i49.val = (i46 ||| i48).val)
    (e50 : i50.val = v11) (h51 : i51.val = (i50 &&& 7#u16).val)
    (h52 : i52.val = i51.val <<< 10 % U16.size) (h54 : i54.val = (i49 ||| i52).val)
    (_b9 : v9 < 256) (_b10 : v10 < 256) (_b11 : v11 < 256) :
    i54.val = (v9 + (2 ^ 8 * v10 + 2 ^ 16 * v11)) / 2 ^ 6 % 2 ^ 13 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have p46 : i46.val = v9 / 2 ^ 6 := by rw [h46, e41, Nat.shiftRight_eq_div_pow]
  have p48 : i48.val = v10 * 2 ^ 2 := by
    rw [h48, e47, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  have p51 : i51.val = v11 % 2 ^ 3 := by
    rw [h51, UScalar.val_and, e50, show ((7#u16).val : ℕ) = 2 ^ 3 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have p52 : i52.val = v11 % 2 ^ 3 * 2 ^ 10 := by
    rw [h52, p51, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  have p49 : i49.val = v9 / 2 ^ 6 + v10 * 2 ^ 2 := by
    rw [h49, UScalar.val_or, p46, p48, lor_mul_of_lt (show v9 / 2 ^ 6 < 2 ^ 2 by omega)]
  rw [h54, UScalar.val_or, p49, p52, lor_mul_of_lt (show v9 / 2 ^ 6 + v10 * 2 ^ 2 < 2 ^ 10 by omega)]
  omega

private theorem coef7 (i50 i55 i56 i57 i59 : U16) (v11 v12 v13 : ℕ)
    (e50 : i50.val = v11) (h55 : i55.val = i50.val >>> 3) (e56 : i56.val = v12)
    (h57 : i57.val = i56.val <<< 5 % U16.size) (h59 : i59.val = (i55 ||| i57).val)
    (_b11 : v11 < 256) (_b12 : v12 < 256) (_b13 : v13 < 256) :
    i59.val = (v11 + (2 ^ 8 * v12 + 2 ^ 16 * v13)) / 2 ^ 3 % 2 ^ 13 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have p55 : i55.val = v11 / 2 ^ 3 := by rw [h55, e50, Nat.shiftRight_eq_div_pow]
  have p57 : i57.val = v12 * 2 ^ 5 := by
    rw [h57, e56, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  rw [h59, UScalar.val_or, p55, p57, lor_mul_of_lt (show v11 / 2 ^ 3 < 2 ^ 5 by omega)]; omega

set_option maxHeartbeats 10000000 in
/-- Loop-invariant version of `deserialize_13_spec`: after processing groups
`[iter.start, 32)`, coefficient `j` in a processed group holds its 13-bit window;
untouched output slots keep their old value. -/
private theorem deserialize_13_loop_spec (bytes : Slice U8) (arr : Array U8 416#usize)
    (harr : arr.val = bytes.val) (hlen : bytes.length = 416)
    (iter : core.ops.range.Range Usize) (out : Array U16 256#usize)
    (hstart : iter.start.val ≤ 32) (hend : iter.«end».val = 32) :
    ser.deserialize_13_loop iter arr out
      ⦃ (r : Array U16 256#usize) =>
          ∀ j (hj : j < 256),
            (r.val[j]'(by have := r.property; grind)).val
              = if j < 8 * iter.start.val then (out.val[j]'(by have := out.property; grind)).val
                else streamNat bytes (13 * j) 13 ⦄ := by
  unfold ser.deserialize_13_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ g, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hg32 : iter.start.val < 32 := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec
    have hb_spec : core.slice.index.SliceIndexRangeUsizeSlice.index
          ({ start := i, «end» := i1 } : core.ops.range.Range Usize) arr.to_slice
        ⦃ (s : Slice U8) => s.val = arr.val.slice i.val i1.val ∧ s.length = i1.val - i.val ⦄ := by
      have hts : arr.to_slice.length = 416 := by simp [Array.to_slice, Slice.length]
      simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, UScalar.le_equiv, Slice.length]
      split
      · simp only [WP.spec_ok, Array.to_slice]; scalar_tac
      · scalar_tac
    let* ⟨ b, hb_val, hb_len ⟩ ← hb_spec
    let* ⟨ o1, ho1 ⟩ ← Std.Usize.mul_spec
    have ho1m : o1.val + 7 ≤ Usize.max := by scalar_tac
    have harrlen : arr.val.length = 416 := by have := arr.property; scalar_tac
    -- Each closure read is byte `13·g + k` of the whole buffer.
    have hclos : ∀ (k : Usize), k.val < 13 →
        ser.deserialize_13.closure.Insts.CoreOpsFunctionFnTupleUsizeU16.call b k
          ⦃ (r : U16) => r.val = (bytes.val[13 * iter.start.val + k.val]!).val ⦄ := by
      intro k hk
      have hkb : k.val < b.length := by rw [hb_len]; scalar_tac
      apply WP.spec_mono (deser13_closure_spec b k hkb)
      intro r hr
      rw [hr]
      have hkbl : k.val < b.val.length := by simp only [Slice.length] at hkb; omega
      rw [(getElem!_pos b.val k.val hkbl).symm, hb_val,
          List.getElem!_slice i.val i1.val k.val arr.val (by rw [harrlen]; omega), harr, hi]
    let* ⟨ i2, hi2 ⟩ ← hclos 0#usize (by scalar_tac)
    let* ⟨ i3, hi3 ⟩ ← hclos 1#usize (by scalar_tac)
    let* ⟨ i4, hi4, hi4bv ⟩ ← UScalar.and_spec
    let* ⟨ i5, hi5, hi5bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i6, hi6, hi6bv ⟩ ← UScalar.or_spec
    let* ⟨ out1, hout1 ⟩ ← Array.update_spec
    let* ⟨ i7, hi7, hi7bv ⟩ ← Std.U16.ShiftRight_IScalar_spec
    let* ⟨ i8, hi8 ⟩ ← hclos 2#usize (by scalar_tac)
    let* ⟨ i9, hi9, hi9bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i10, hi10, hi10bv ⟩ ← UScalar.or_spec
    let* ⟨ i11, hi11 ⟩ ← hclos 3#usize (by scalar_tac)
    let* ⟨ i12, hi12, hi12bv ⟩ ← UScalar.and_spec
    let* ⟨ i13, hi13, hi13bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i14, hi14 ⟩ ← Std.Usize.add_spec
    let* ⟨ i15, hi15, hi15bv ⟩ ← UScalar.or_spec
    let* ⟨ out2, hout2 ⟩ ← Array.update_spec
    let* ⟨ i16, hi16, hi16bv ⟩ ← Std.U16.ShiftRight_IScalar_spec
    let* ⟨ i17, hi17 ⟩ ← hclos 4#usize (by scalar_tac)
    let* ⟨ i18, hi18, hi18bv ⟩ ← UScalar.and_spec
    let* ⟨ i19, hi19, hi19bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i20, hi20 ⟩ ← Std.Usize.add_spec
    let* ⟨ i21, hi21, hi21bv ⟩ ← UScalar.or_spec
    let* ⟨ out3, hout3 ⟩ ← Array.update_spec
    let* ⟨ i22, hi22, hi22bv ⟩ ← Std.U16.ShiftRight_IScalar_spec
    let* ⟨ i23, hi23 ⟩ ← hclos 5#usize (by scalar_tac)
    let* ⟨ i24, hi24, hi24bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i25, hi25, hi25bv ⟩ ← UScalar.or_spec
    let* ⟨ i26, hi26 ⟩ ← hclos 6#usize (by scalar_tac)
    let* ⟨ i27, hi27, hi27bv ⟩ ← UScalar.and_spec
    let* ⟨ i28, hi28, hi28bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i29, hi29 ⟩ ← Std.Usize.add_spec
    let* ⟨ i30, hi30, hi30bv ⟩ ← UScalar.or_spec
    let* ⟨ out4, hout4 ⟩ ← Array.update_spec
    let* ⟨ i31, hi31, hi31bv ⟩ ← Std.U16.ShiftRight_IScalar_spec
    let* ⟨ i32, hi32 ⟩ ← hclos 7#usize (by scalar_tac)
    let* ⟨ i33, hi33, hi33bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i34, hi34, hi34bv ⟩ ← UScalar.or_spec
    let* ⟨ i35, hi35 ⟩ ← hclos 8#usize (by scalar_tac)
    let* ⟨ i36, hi36, hi36bv ⟩ ← UScalar.and_spec
    let* ⟨ i37, hi37, hi37bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i38, hi38 ⟩ ← Std.Usize.add_spec
    let* ⟨ i39, hi39, hi39bv ⟩ ← UScalar.or_spec
    let* ⟨ out5, hout5 ⟩ ← Array.update_spec
    let* ⟨ i40, hi40, hi40bv ⟩ ← Std.U16.ShiftRight_IScalar_spec
    let* ⟨ i41, hi41 ⟩ ← hclos 9#usize (by scalar_tac)
    let* ⟨ i42, hi42, hi42bv ⟩ ← UScalar.and_spec
    let* ⟨ i43, hi43, hi43bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i44, hi44 ⟩ ← Std.Usize.add_spec
    let* ⟨ i45, hi45, hi45bv ⟩ ← UScalar.or_spec
    let* ⟨ out6, hout6 ⟩ ← Array.update_spec
    let* ⟨ i46, hi46, hi46bv ⟩ ← Std.U16.ShiftRight_IScalar_spec
    let* ⟨ i47, hi47 ⟩ ← hclos 10#usize (by scalar_tac)
    let* ⟨ i48, hi48, hi48bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i49, hi49, hi49bv ⟩ ← UScalar.or_spec
    let* ⟨ i50, hi50 ⟩ ← hclos 11#usize (by scalar_tac)
    let* ⟨ i51, hi51, hi51bv ⟩ ← UScalar.and_spec
    let* ⟨ i52, hi52, hi52bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i53, hi53 ⟩ ← Std.Usize.add_spec
    let* ⟨ i54, hi54, hi54bv ⟩ ← UScalar.or_spec
    let* ⟨ out7, hout7 ⟩ ← Array.update_spec
    let* ⟨ i55, hi55, hi55bv ⟩ ← Std.U16.ShiftRight_IScalar_spec
    let* ⟨ i56, hi56 ⟩ ← hclos 12#usize (by scalar_tac)
    let* ⟨ i57, hi57, hi57bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i58, hi58 ⟩ ← Std.Usize.add_spec
    let* ⟨ i59, hi59, hi59bv ⟩ ← UScalar.or_spec
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hc0 : i6.val = streamNat bytes (13 * (8 * iter.start.val + 0)) 13 := by
      rw [show 13 * (8 * iter.start.val + 0) = 8 * (13 * iter.start.val + 0) + 0 from by ring,
          streamNat_window bytes (13 * iter.start.val + 0) 0 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef0 i2 i3 i4 i5 i6 _ _ _ hi2 hi3 hi4 hi5 hi6
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hc1 : i15.val = streamNat bytes (13 * (8 * iter.start.val + 1)) 13 := by
      rw [show 13 * (8 * iter.start.val + 1) = 8 * (13 * iter.start.val + 1) + 5 from by ring,
          streamNat_window bytes (13 * iter.start.val + 1) 5 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef1 i3 i7 i8 i9 i10 i11 i12 i13 i15 _ _ _ hi3 hi7 hi8 hi9 hi10 hi11 hi12 hi13 hi15
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hc2 : i21.val = streamNat bytes (13 * (8 * iter.start.val + 2)) 13 := by
      rw [show 13 * (8 * iter.start.val + 2) = 8 * (13 * iter.start.val + 3) + 2 from by ring,
          streamNat_window bytes (13 * iter.start.val + 3) 2 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef2 i11 i16 i17 i18 i19 i21 _ _ _ hi11 hi16 hi17 hi18 hi19 hi21
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hc3 : i30.val = streamNat bytes (13 * (8 * iter.start.val + 3)) 13 := by
      rw [show 13 * (8 * iter.start.val + 3) = 8 * (13 * iter.start.val + 4) + 7 from by ring,
          streamNat_window bytes (13 * iter.start.val + 4) 7 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef3 i17 i22 i23 i24 i25 i26 i27 i28 i30 _ _ _ hi17 hi22 hi23 hi24 hi25 hi26 hi27 hi28 hi30
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hc4 : i39.val = streamNat bytes (13 * (8 * iter.start.val + 4)) 13 := by
      rw [show 13 * (8 * iter.start.val + 4) = 8 * (13 * iter.start.val + 6) + 4 from by ring,
          streamNat_window bytes (13 * iter.start.val + 6) 4 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef4 i26 i31 i32 i33 i34 i35 i36 i37 i39 _ _ _ hi26 hi31 hi32 hi33 hi34 hi35 hi36 hi37 hi39
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hc5 : i45.val = streamNat bytes (13 * (8 * iter.start.val + 5)) 13 := by
      rw [show 13 * (8 * iter.start.val + 5) = 8 * (13 * iter.start.val + 8) + 1 from by ring,
          streamNat_window bytes (13 * iter.start.val + 8) 1 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef5 i35 i40 i41 i42 i43 i45 _ _ _ hi35 hi40 hi41 hi42 hi43 hi45
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hc6 : i54.val = streamNat bytes (13 * (8 * iter.start.val + 6)) 13 := by
      rw [show 13 * (8 * iter.start.val + 6) = 8 * (13 * iter.start.val + 9) + 6 from by ring,
          streamNat_window bytes (13 * iter.start.val + 9) 6 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef6 i41 i46 i47 i48 i49 i50 i51 i52 i54 _ _ _ hi41 hi46 hi47 hi48 hi49 hi50 hi51 hi52 hi54
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hc7 : i59.val = streamNat bytes (13 * (8 * iter.start.val + 7)) 13 := by
      rw [show 13 * (8 * iter.start.val + 7) = 8 * (13 * iter.start.val + 11) + 3 from by ring,
          streamNat_window bytes (13 * iter.start.val + 11) 3 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef7 i50 i55 i56 i57 i59 _ _ _ hi50 hi55 hi56 hi57 hi59
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    -- recurse on the remaining groups
    have hstartnew : iter1.start.val ≤ 32 := by rw [hstart']; omega
    have hendnew : iter1.«end».val = 32 := by rw [hend']; exact hend
    apply WP.spec_mono (deserialize_13_loop_spec bytes arr harr hlen iter1 a hstartnew hendnew)
    intro r hr j hj
    have ihj := hr j hj
    rw [hstart'] at ihj
    by_cases hjA : j < 8 * iter.start.val
    · -- slot untouched by this group
      rw [if_pos hjA, ihj, if_pos (by omega : j < 8 * (iter.start.val + 1))]
      simp only [ha, hout7, hout6, hout5, hout4, hout3, hout2, hout1, Array.set_val_eq,
        ho1, hi14, hi20, hi29, hi38, hi44, hi53, hi58]
      simp_lists
    · by_cases hjC : j < 8 * (iter.start.val + 1)
      · -- slot written by this group: `j = 8·g + t`
        rw [if_neg hjA, ihj, if_pos hjC]
        obtain ⟨t, htlt, rfl⟩ : ∃ t, t < 8 ∧ j = 8 * iter.start.val + t :=
          ⟨j - 8 * iter.start.val, by omega, by omega⟩
        rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 by omega)
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals
          (simp only [ha, hout7, hout6, hout5, hout4, hout3, hout2, hout1, Array.set_val_eq,
            ho1, hi14, hi20, hi29, hi38, hi44, hi53, hi58]
           simp_lists
           first
           | exact hc0 | exact hc1 | exact hc2 | exact hc3
           | exact hc4 | exact hc5 | exact hc6 | exact hc7)
      · -- slot in a later group: both sides are its window
        rw [if_neg hjA, ihj, if_neg hjC]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro j hj
    rw [if_pos (by scalar_tac)]

/-- Decoding-correctness of `deserialize_13`: every coefficient equals the 13-bit
little-endian stream window the generic decoder would produce. -/
theorem deserialize_13_spec (bytes : Slice U8) (arr : Array U8 416#usize)
    (harr : arr.val = bytes.val) (hlen : bytes.length = 416) :
    ser.deserialize_13 arr
      ⦃ (r : Array U16 256#usize) =>
          ∀ j (hj : j < 256),
            (r.val[j]'(by have := r.property; grind)).val = streamNat bytes (13 * j) 13 ⦄ := by
  unfold ser.deserialize_13
  apply WP.spec_mono (deserialize_13_loop_spec bytes arr harr hlen
    { start := 0#usize, «end» := 32#usize } (Array.repeat 256#usize 0#u16) (by simp) (by simp))
  intro r hr j hj
  have h := hr j hj
  rwa [if_neg (by simp)] at h

/-- **Correctness of `RingElem::deserialize` at 13 bits.**  Decoding a 416-byte
buffer yields the spec ring element `deserialize 13`.  (The Rust method was renamed
from `from_bytes` to `deserialize`; the 13-bit branch now routes through the
branchless `deserialize_13` fast path.) -/
theorem from_bytes_spec (bytes : Slice U8) (hlen : bytes.length = 32 * 13) :
    arithmetic.ring_arith.RingElem.deserialize bytes 13#usize
      ⦃ (r : RingElem) =>
          toRingElem13 r = Spec.Kopis.deserialize 13 (sliceToBytes bytes (32 * 13) hlen) ⦄ := by
  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG, consts.MODULUS_Q_BITS]
  have hlen416 : bytes.length = 416 := by omega
  step*
  -- resolve `try_from 416` (lengths match) and `unwrap`, exposing `arr.val = bytes.val`
  have hb : bytes.len = 416#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
    core.result.Result.unwrap]
  apply WP.spec_bind (deserialize_13_spec bytes ⟨bytes.val, by scalar_tac⟩ rfl hlen416)
  intro r hr
  simp only [WP.spec_ok]
  apply Vector.ext
  intro jj hjj
  simp only [toRingElem13, Vector.getElem_ofFn]
  rw [deserialize_get 13 (sliceToBytes bytes (32 * 13) hlen) jj hjj]
  have hval := hr jj hjj
  rw [hval, streamNat_eq_sum bytes 13 jj hlen hjj]

end Kopis.Properties
