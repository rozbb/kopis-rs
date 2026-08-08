/-
  # Kopis/Keccak/Conform.lean — the register squeeze stream is TurboSHAKE's.

  Two statements are proved elsewhere and are completely independent of each other:

  * each backend's `xofN` file — sponge `l`'s output is `squeezeByte (absorbed …) RATE`;
  * `Spec/TurboSHAKE`'s `turboSHAKE_oneBlock_getElem` — byte `i` of `turboSHAKE` is
    `(KP_bytes^[i / rate + 1] st)[i % rate]`.

  This file shows the two right-hand sides are the same function, which needs three things: the
  states agree (`absorbed_eq`), the permutations agree (`sqState_KP`, from `KPBridge.lean`), and
  the byte readouts agree (`wordByte_leWordB`).  Nothing here touches an extraction, so both
  backends share it; each one only supplies its own `xofN` half.
-/
import Kopis.Keccak.KPBridge
import Kopis.Keccak.Squeeze

open Aeneas Aeneas.Std
open Kopis.Bits
open Spec.SHA3
open Spec (𝔹 bytesToBits)

namespace Kopis.Keccak

set_option maxHeartbeats 4000000

noncomputable section

/-- Squeezing `n` times on the word view is iterating `KP_bytes` `n` times on the byte view. -/
theorem sqState_KP (st : 𝔹 200) (n : ℕ) :
    sqState (fun x y => leWordB st (8 * idx x y)) n
      = fun x y => leWordB (Spec.TurboSHAKE.KP_bytes^[n] st) (8 * idx x y) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sqState_succ, ih]
    funext x y
    rw [Function.iterate_succ_apply', leWordB_KP_bytes]

/-- Byte `k` of the word view is byte `k` of the byte view. -/
theorem wordByte_leWordB (st : 𝔹 200) (k : ℕ) (hk : k < 200) :
    wordByte (fun x y => leWordB st (8 * idx x y)) k = st[k]! := by
  rw [wordByte, idx_coord (k / 8) (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro m hm
  rw [getLsbD_laneOf]
  simp only [hm, decide_true, Bool.true_and]
  rw [getLsbD_leWordB _ _ _ (by omega),
    show 8 * (k / 8) + (8 * (k % 8) + m) / 8 = k from by omega,
    show (8 * (k % 8) + m) % 8 = m from by omega]

/-- **The squeeze streams agree.**  `keccak.rs`'s output byte and `turboSHAKE`'s output byte are
the same function of the start state — the register side read as words, the spec side as bytes. -/
theorem squeezeByte_eq (st : 𝔹 200) (RATE k : ℕ) (hR : 0 < RATE) (hR200 : RATE ≤ 200) :
    squeezeByte (fun x y => leWordB st (8 * idx x y)) RATE k
      = (Spec.TurboSHAKE.KP_bytes^[k / RATE + 1] st)[k % RATE]! := by
  rw [squeezeByte, sqState_KP,
    wordByte_leWordB _ _ (by have := Nat.mod_lt k hR; omega)]

theorem getLsbD_leWordOf (f : ℕ → Std.U8) (off z : ℕ) (hz : z < 64) :
    (leWordOf f off).getLsbD z = ((f (off + z / 8)).bv).getLsbD (z % 8) := by
  rw [BitVec.getLsbD_eq_getElem hz, leWordOf, BitVec.getElem_ofFn]

/-- **The absorbed states agree.**  The register array after absorbing the padded block is the
spec's start state, read as words. -/
theorem absorbed_eq (RATE : ℕ) (DS : Std.U8) (pre suf : List Std.U8) (st : 𝔹 200)
    (hR200 : RATE ≤ 200) (hfit : 32 + suf.length + 1 < RATE)
    (hst : ∀ j < 200, st[j]! = (padByte RATE DS pre suf j).bv) :
    absorbed RATE DS pre suf = fun x y => leWordB st (8 * idx x y) := by
  funext x y
  have hlt := idx_lt x y
  rw [absorbed]
  by_cases hk : 8 * idx x y < RATE
  · rw [if_pos hk]
    apply BitVec.eq_of_getLsbD_eq
    intro z hz
    rw [getLsbD_leWordOf _ _ _ hz, getLsbD_leWordB _ _ _ hz, hst _ (by omega)]
  · rw [if_neg hk]
    apply BitVec.eq_of_getLsbD_eq
    intro z hz
    rw [getLsbD_leWordB _ _ _ hz, hst _ (by omega), padByte]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

/-! ## The conformance statement -/

/-- An extracted byte array as a spec byte vector. -/
def bytesOf {n : Std.Usize} (a : Std.Array Std.U8 n) : 𝔹 (n : ℕ) :=
  Vector.ofFn fun (i : Fin (n : ℕ)) => (a.val[i.val]'(by have := a.property; omega)).bv

theorem getElem!_bytesOf {n : Std.Usize} (a : Std.Array Std.U8 n) (j : ℕ) (hj : j < (n : ℕ)) :
    (bytesOf a)[j]! = (a.val[j]!).bv := by
  rw [getElem!_pos _ j (by simpa using hj), bytesOf, Vector.getElem_ofFn,
    getElem!_pos a.val j (by rw [a.property]; exact hj)]

/-- The message `xof4` hashes in lane `l`: the shared prefix followed by that lane's suffix. -/
def msgOf {S : Std.Usize} (pre : Std.Array Std.U8 32#usize) (suf : Std.Array Std.U8 S) :
    𝔹 (32 + S.val) :=
  ((bytesOf pre) ++ (bytesOf suf)).cast (by simp)

theorem getElem!_msgOf {S : Std.Usize} (pre : Std.Array Std.U8 32#usize)
    (suf : Std.Array Std.U8 S) (j : ℕ) (hj : j < 32 + S.val) :
    (msgOf pre suf)[j]!
      = if j < 32 then (pre.val[j]!).bv else (suf.val[j - 32]!).bv := by
  rw [getElem!_pos _ j (by simpa using hj), msgOf]
  simp only [Vector.getElem_cast, Vector.getElem_append]
  by_cases h : j < 32
  · rw [dif_pos (by simpa using h), if_pos h, ← getElem!_pos _ j (by simpa using h),
      getElem!_bytesOf pre j (by simpa using h)]
  · rw [dif_neg (by simpa using h), if_neg h,
      ← getElem!_pos (bytesOf suf) _ (show j - ((32#usize : Std.Usize) : ℕ) < _ by simp; omega)]
    exact getElem!_bytesOf suf (j - 32) (by omega)

/-- The padded block as a spec state. -/
def padState (RATE : ℕ) (DS : Std.U8) (pre suf : List Std.U8) : 𝔹 200 :=
  Vector.ofFn fun (j : Fin 200) => (padByte RATE DS pre suf j.val).bv

theorem getElem!_padState (RATE : ℕ) (DS : Std.U8) (pre suf : List Std.U8) (j : ℕ)
    (hj : j < 200) : (padState RATE DS pre suf)[j]! = (padByte RATE DS pre suf j).bv := by
  rw [getElem!_pos _ j hj, padState, Vector.getElem_ofFn]

end

end Kopis.Keccak
