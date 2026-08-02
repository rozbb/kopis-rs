/-
  # Kopis/Bits/Stream.lean — the little-endian bit stream both backends decode.

  A serialized ring element is a little-endian bit stream: bit `m` is bit `m % 8` of byte
  `m / 8`, and coefficient `j` of a `w`-bit encoding is the window `[w·j, w·j + w)`.  That is
  the *only* thing the portable unpacker and the AVX2 one have in common — one walks the stream
  with a sliding `u32` window, the other extracts eight coefficients at a time with a shuffle
  and a variable shift — so it is what they are both proved against, and hence what their
  equality is proved through.

  Nothing here mentions an extracted constant or a backend, which is why it lives outside
  `Kopis/Properties/` (the serial proofs) and `Kopis/Avx2/`: both import it.
-/
import Aeneas

open Aeneas Aeneas.Std Result
open scoped BigOperators

namespace Kopis.Properties


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

/-! ## Reading the stream through a fixed-size window

The sliding-window decoder consumes the stream a byte at a time, so `streamNat_byte` above is
all it needs.  The vector decoder does something different: it loads a *fixed* four-byte window
per coefficient and shifts it down by the coefficient's bit offset within its first byte.  The
lemmas here say those agree — that a `len`-bit field starting at bit `8·base + sh` is the
four-byte window at `base`, shifted right by `sh` and truncated.

The window may reach past the end of the buffer (the last coefficient of a block does), which
is harmless and is why this is stated over `streamByte`: `getElem!` reads out of range as `0`,
matching both the zero-padded scratch buffer the AVX2 code loads from and the zero bits
`streamBit` reports there. -/

/-- Byte `i` of the stream, and `0` past the end — the same read `streamBit` performs. -/
def streamByte (bytes : Slice U8) (i : ℕ) : ℕ := (bytes.val[i]!).val

theorem streamByte_lt (bytes : Slice U8) (i : ℕ) : streamByte bytes i < 256 := by
  unfold streamByte; scalar_tac

/-- Base-256 digits: the low `n` bytes of `u`, reassembled, are `u % 256ⁿ`. -/
theorem sum_base256 (u : ℕ) :
    ∀ n, ∑ b ∈ Finset.range n, (u >>> (8 * b)) % 256 * 256 ^ b = u % 256 ^ n := by
  intro n
  induction n with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul, Nat.shiftRight_eq_div_pow,
      show (2:ℕ) ^ (8 * m) = 256 ^ m from by
        rw [show (256:ℕ) = 2 ^ 8 from by norm_num, ← pow_mul, Nat.mul_comm]]
    ring

/-- A little-endian byte sequence, bit by bit: bit `j` of the assembled number is bit `j % 8`
of byte `j / 8`. -/
theorem testBit_sum_bytes :
    ∀ (n : ℕ) (f : ℕ → ℕ), (∀ i, f i < 256) → ∀ j < 8 * n,
      (∑ b ∈ Finset.range n, f b * 256 ^ b).testBit j = (f (j / 8)).testBit (j % 8) := by
  intro n
  induction n with
  | zero => intro f _ j hj; omega
  | succ m ih =>
    intro f hf j hj
    rw [Finset.sum_range_succ' (fun b => f b * 256 ^ b) m]
    have hre : (∑ b ∈ Finset.range m, f (b + 1) * 256 ^ (b + 1)) + f 0 * 256 ^ 0
        = 2 ^ 8 * (∑ b ∈ Finset.range m, f (b + 1) * 256 ^ b) + f 0 := by
      rw [Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro b _
        rw [pow_succ, show (256:ℕ) = 2 ^ 8 from by norm_num]; ring
      · simp
    rw [hre, Nat.testBit_two_pow_mul_add _ (by simpa using hf 0) j]
    by_cases hj8 : j < 8
    · rw [if_pos hj8, show j / 8 = 0 from by omega, show j % 8 = j from by omega]
    · rw [if_neg hj8, ih (fun b => f (b + 1)) (fun i => hf (i + 1)) (j - 8) (by omega),
        show (j - 8) / 8 + 1 = j / 8 from by omega,
        show (j - 8) % 8 = j % 8 from by omega]

/-- **The window lemma.**  The `len`-bit field at bit `8·base + sh` is the four-byte window at
`base`, shifted down by `sh` and truncated — which is exactly what one `vpshufb` + `vpsrlvd` +
`vpand` lane computes.  Four bytes suffice because `sh ≤ 7` and `len ≤ 25`. -/
theorem streamNat_of_byteWindow (bytes : Slice U8) (base sh len : ℕ) (hlen : sh + len ≤ 32) :
    streamNat bytes (8 * base + sh) len
      = ((∑ b ∈ Finset.range 4, streamByte bytes (base + b) * 256 ^ b) >>> sh) % 2 ^ len := by
  set W := ∑ b ∈ Finset.range 4, streamByte bytes (base + b) * 256 ^ b with hW
  have hbit : ∀ j < 32, W.testBit j = (streamByte bytes (base + j / 8)).testBit (j % 8) := by
    intro j hj
    rw [hW, testBit_sum_bytes 4 (fun b => streamByte bytes (base + b))
      (fun i => streamByte_lt bytes (base + i)) j (by omega)]
  simp only [streamByte] at hbit
  rw [← sum_testBit_eq_mod]
  unfold streamNat
  apply Finset.sum_congr rfl
  intro c hc
  simp only [Finset.mem_range] at hc
  congr 1
  unfold streamBit
  rw [show (8 * base + sh + c) / 8 = base + (sh + c) / 8 from by omega,
      show (8 * base + sh + c) % 8 = (sh + c) % 8 from by omega,
      ← hbit (sh + c) (by omega), Nat.testBit_shiftRight]

/-! ## Population counts over the stream

The centred binomial sampler counts the set bits of a `half`-bit window.  Both backends compute
that count — the portable one bit by bit, the AVX2 one with a nibble `vpshufb` lookup — so, like
`streamNat`, it is defined once here and both are proved against it.

`cbdX` was `Kopis/Properties/GenSecretLoops.lean`'s; it is backend-agnostic and moved here so the
AVX2 sampler can be stated through the same object rather than a copy. -/

/-- Popcount of the `half`-bit stream window at `p`. -/
def cbdX (buf : Slice U8) (half p : ℕ) : ℕ := ∑ i ∈ Finset.range half, streamBit buf (p + i)

theorem cbdX_le (buf : Slice U8) (half p : ℕ) : cbdX buf half p ≤ half := by
  unfold cbdX
  calc ∑ i ∈ Finset.range half, streamBit buf (p + i)
      ≤ ∑ _i ∈ Finset.range half, 1 := Finset.sum_le_sum (fun i _ => streamBit_le_one buf (p + i))
    _ = half := by simp

/-- Bit `i` of a stream window is the stream's bit — the fact that lets a popcount of the
*extracted field* be read as a popcount of the *stream*, which is what the vector sampler needs
(it counts bits of the deserializer's output, not of the buffer). -/
theorem testBit_streamNat (bytes : Slice U8) (lo len i : ℕ) (hi : i < len) :
    ((streamNat bytes lo len).testBit i).toNat = streamBit bytes (lo + i) := by
  have hsplit : streamNat bytes lo len
      = streamNat bytes lo i + 2 ^ i * streamNat bytes (lo + i) (len - i) := by
    conv_lhs => rw [show len = i + (len - i) from by omega]
    rw [streamNat_split]
  have hlt : streamNat bytes lo i < 2 ^ i := streamNat_lt _ _ _
  have hcomm : streamNat bytes lo i + 2 ^ i * streamNat bytes (lo + i) (len - i)
      = 2 ^ i * streamNat bytes (lo + i) (len - i) + streamNat bytes lo i := by ring
  rw [hsplit, hcomm, Nat.testBit_two_pow_mul_add _ hlt, if_neg (by omega), Nat.sub_self]
  -- bit 0 of the remaining window is its first stream bit
  have htail : streamNat bytes (lo + i) (len - i)
      = streamNat bytes (lo + i) 1 + 2 * streamNat bytes (lo + i + 1) (len - i - 1) := by
    conv_lhs => rw [show len - i = 1 + (len - i - 1) from by omega]
    rw [streamNat_split]
    norm_num
  have hone : streamNat bytes (lo + i) 1 = streamBit bytes (lo + i) := by
    simp [streamNat]
  have hb : streamBit bytes (lo + i) ≤ 1 := streamBit_le_one _ _
  rw [htail, hone, Nat.testBit_zero]
  rcases Nat.eq_zero_or_pos (streamBit bytes (lo + i)) with h0 | h1
  · simp [h0, Nat.add_mul_mod_self_left]
  · have : streamBit bytes (lo + i) = 1 := by omega
    simp [this, Nat.add_mul_mod_self_left]

/-- The popcount of a stream window, as a popcount of its *value*. -/
theorem cbdX_eq_bitSum (bytes : Slice U8) (half p : ℕ) :
    cbdX bytes half p
      = ∑ i ∈ Finset.range half, ((streamNat bytes p half).testBit i).toNat := by
  unfold cbdX
  exact (Finset.sum_congr rfl fun i hi =>
    testBit_streamNat bytes p half i (Finset.mem_range.mp hi)).symm

/-! ## Masking and shifting a window

The sampler splits each `MU`-bit field into two `MU/2`-bit halves with a mask and a shift.  On
the stream those are just shorter windows. -/

/-- Masking a window to its low `k` bits is the shorter window. -/
theorem streamNat_mod (bytes : Slice U8) (p len k : ℕ) (h : k ≤ len) :
    streamNat bytes p len % 2 ^ k = streamNat bytes p k := by
  conv_lhs => rw [show len = k + (len - k) from by omega, streamNat_split]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (streamNat_lt _ _ _)]

/-- Shifting a window down by `k` is the window starting `k` bits later. -/
theorem streamNat_shiftRight (bytes : Slice U8) (p len k : ℕ) (h : k ≤ len) :
    streamNat bytes p len >>> k = streamNat bytes (p + k) (len - k) := by
  conv_lhs => rw [show len = k + (len - k) from by omega, streamNat_split]
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ k),
    Nat.div_eq_of_lt (streamNat_lt _ _ _), Nat.zero_add]

/-- A popcount taken over more bits than the window has counts the same bits: the extra ones are
zero.  This is what lets `popcount_small`, which always sums five bits, compute a `half`-bit
popcount for any `half ≤ 5`. -/
theorem cbdX_eq_bitSum_of_le (bytes : Slice U8) (half p n : ℕ) (h : half ≤ n) :
    ∑ i ∈ Finset.range n, ((streamNat bytes p half).testBit i).toNat = cbdX bytes half p := by
  rw [show n = half + (n - half) from by omega, Finset.sum_range_add]
  have hzero : ∀ i ∈ Finset.range (n - half),
      ((streamNat bytes p half).testBit (half + i)).toNat = 0 := by
    intro i _
    rw [Nat.testBit_lt_two_pow
      (lt_of_lt_of_le (streamNat_lt bytes p half) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rfl
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, Nat.add_zero, cbdX_eq_bitSum]

/-- The sampler's coefficient, as the wrapping `u16` difference of the two halves' popcounts. -/
def cbdU16 (buf : Slice U8) (half p : ℕ) : ℕ :=
  (cbdX buf half p + 2 ^ 16 - cbdX buf half (p + half)) % 2 ^ 16

end Kopis.Properties
