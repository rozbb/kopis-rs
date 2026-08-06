import Spec.SHA3.Spec

/-!
# TurboSHAKE specification (RFC 9861)

TurboSHAKE128 and TurboSHAKE256 are eXtendable-Output Functions (XOFs) built on
`Keccak-p[1600, n_r=12]`, a round-reduced variant of the permutation used by the
SHA-3 and SHAKE functions (FIPS 202). Halving the number of rounds from 24 to 12
makes TurboSHAKE roughly twice as fast as the corresponding SHAKE functions,
while keeping the same claimed security strength.

## Rate and capacity (RFC 9861, Table 1)

| Function       | Rate      | Capacity |
|----------------|-----------|----------|
| TurboSHAKE128  | 168 bytes | 32 bytes |
| TurboSHAKE256  | 136 bytes | 64 bytes |

## Padding (§2.2)

TurboSHAKE forms the sponge input `M' = M ‖ D`, where `D ∈ [0x01, 0x7F]` is a
domain separation byte. `M'` is zero-padded to a multiple of `rate` bytes, and
`0x80` is XORed into byte `rate − 1` of the final block. This "equivalently
implements the pad10*1 rule" (§2.2): the low bit of `D` supplies pad10*1's first
`1`, `D`'s cleared MSB leaves room for the trailing `1`, and the `0x80` supplies
that trailing `1`.

## Mechanization notes

- The permutation reuses `Spec.SHA3.KECCAK_p 12` (only the round count differs
  from SHAKE, which uses `KECCAK_p 24 = KECCAK_f`).
- The sponge is described directly at the byte level (`𝔹 200` state), matching
  the reference pseudocode of Appendices A.2–A.3. `KP_bytes` bridges to the
  bit-level permutation via `bytesToBits`/`bitsToBytes`; these use the same
  LSB-first byte ordering that SHA-3 relies on (see `Spec.SHA3.shake128`), so
  the byte-level state and the 1600-bit permutation state agree.
- `absorb`/`squeeze` are written as structurally-terminating recursions rather
  than as `while` loops, so `squeeze` can return a `𝔹 outLen` with no size
  side-condition to discharge downstream.

## References

- RFC 9861, §2.1–2.2 and Appendices A.1–A.3
- FIPS 202, §3.3 (the `Keccak-p` permutation)
-/

namespace Spec.TurboSHAKE

open Spec (𝔹 bytesToBits bitsToBytes)
open Spec.SHA3 (b KECCAK_p)

/-! ## Permutation (RFC 9861, Appendix A.1) -/

/-- `KP` — the `Keccak-p[1600, n_r=12]` permutation, i.e. the SHA-3 permutation
    reduced to its last 12 rounds (§2.2). -/
def KP (S : Vector Bool b) : Vector Bool b := KECCAK_p 12 S

/-- `KP` at the byte level: 200-byte state → 1600-bit state → `KP` → 200 bytes. -/
def KP_bytes (state : 𝔹 200) : 𝔹 200 :=
  bitsToBytes (KP (bytesToBits state))

/-! ## Sponge helpers -/

/-- XOR `len` bytes taken from `src` (starting at index `srcOff`) into positions
    `0 .. len-1` of a 200-byte state. Positions `≥ len` are left unchanged, which
    models `state ^= block ‖ 00^capacity` in the pseudocode. -/
private def xorBytesAt (state : 𝔹 200) (src : Array Byte) (srcOff len : Nat) : 𝔹 200 :=
  Vector.ofFn fun (i : Fin 200) =>
    if i.val < len then
      if h : srcOff + i.val < src.size then
        state[i] ^^^ src[srcOff + i.val]
      else
        state[i]
    else
      state[i]

/-! ## Absorb and squeeze (RFC 9861, §2.2, Appendices A.2–A.3) -/

/-- Absorb phase.

    Process `input = M ‖ D` through the sponge. Each complete `rate`-byte block
    is XORed into the state and followed by an application of `KP`. The final
    (possibly partial) block is zero-padded, has `0x80` XORed into byte
    `rate − 1`, and is followed by one last application of `KP`. -/
private def absorb (state : 𝔹 200) (input : Array Byte) (offset rate : Nat)
    (hrate : 0 < rate) (hrate200 : rate ≤ 200) : 𝔹 200 :=
  if h : offset + rate < input.size then
    let state := xorBytesAt state input offset rate
    absorb (KP_bytes state) input (offset + rate) rate hrate hrate200
  else
    let lastLen := input.size - offset
    let state := xorBytesAt state input offset lastLen
    have h_idx : rate - 1 < 200 := by omega
    let state := state.set (rate - 1) (state[rate - 1] ^^^ (0x80 : Byte)) h_idx
    KP_bytes state
termination_by input.size - offset
decreasing_by omega

/-- Squeeze phase.

    Emit `remaining` output bytes. Each output block is the first `rate` bytes of
    the current state; `KP` is applied between successive blocks. The final
    (possibly short) block requires no trailing `KP`. -/
private def squeeze (state : 𝔹 200) (rate remaining : Nat)
    (hrate : 0 < rate) (hrate200 : rate ≤ 200) : 𝔹 remaining :=
  if h : remaining ≤ rate then
    Vector.ofFn fun (i : Fin remaining) => state[i.val]'(by omega)
  else
    let firstBlock : 𝔹 rate := Vector.ofFn fun (i : Fin rate) => state[i.val]'(by omega)
    let rest := squeeze (KP_bytes state) rate (remaining - rate) hrate hrate200
    (firstBlock ++ rest).cast (by omega)
termination_by remaining
decreasing_by omega

/-- `TurboSHAKE` (RFC 9861, §2.2), parameterized by the `rate` in bytes.

    - `msg`    — the input message `M`
    - `D`      — the domain separation byte; the spec requires `D ∈ [0x01, 0x7F]`
    - `outLen` — the requested output length `L`, in bytes

    The two public instances below fix `rate` to `168` (TurboSHAKE128) and `136`
    (TurboSHAKE256). -/
def turboSHAKE {mLen : Nat} (rate : Nat) (msg : 𝔹 mLen) (D : Byte) (outLen : Nat)
    (hrate : 0 < rate ∧ rate ≤ 200 := by omega) : 𝔹 outLen :=
  let input := msg.toArray.push D
  let state : 𝔹 200 := Vector.replicate 200 (0 : Byte)
  let state := absorb state input 0 rate hrate.1 hrate.2
  squeeze state rate outLen hrate.1 hrate.2

/-! ## TurboSHAKE128 and TurboSHAKE256 (RFC 9861, §2.2, Table 1) -/

/-- `TurboSHAKE128(M, D, L)` — rate 168 bytes, capacity 32 bytes. -/
def turboSHAKE128 {n : Nat} (msg : 𝔹 n) (D : Byte) (outLen : Nat) : 𝔹 outLen :=
  turboSHAKE 168 msg D outLen

/-- `TurboSHAKE256(M, D, L)` — rate 136 bytes, capacity 64 bytes. -/
def turboSHAKE256 {n : Nat} (msg : 𝔹 n) (D : Byte) (outLen : Nat) : 𝔹 outLen :=
  turboSHAKE 136 msg D outLen

/-! ## XOF prefix (streaming) property

The squeeze stream is independent of the requested output length: requesting more
bytes only extends the sequence.  Formally, byte `i` of `turboSHAKE rate msg D a`
equals byte `i` of `turboSHAKE rate msg D b` whenever `i < a` and `i < b`.  This is
what lets a streaming reader consume the XOF in several `read`s. -/

private theorem squeeze_getElem_lt (state : 𝔹 200) (rate rem : Nat) (h1 : 0 < rate)
    (h2 : rate ≤ 200) (i : Nat) (hir : i < rate) (hi : i < rem) :
    (squeeze state rate rem h1 h2)[i]'hi = state[i]'(by omega) := by
  rw [squeeze]
  by_cases h : rem ≤ rate
  · rw [dif_pos h]; simp only [Vector.getElem_ofFn]
  · rw [dif_neg h, Vector.getElem_cast, Vector.getElem_append_left (by omega),
      Vector.getElem_ofFn]

private theorem squeeze_getElem_ge (state : 𝔹 200) (rate rem : Nat) (h1 : 0 < rate)
    (h2 : rate ≤ 200) (i : Nat) (hge : rate ≤ i) (hi : i < rem) :
    (squeeze state rate rem h1 h2)[i]'hi
      = (squeeze (KP_bytes state) rate (rem - rate) h1 h2)[i - rate]'(by omega) := by
  rw [squeeze, dif_neg (by omega : ¬ rem ≤ rate), Vector.getElem_cast,
    Vector.getElem_append_right (by omega)]
  omega

private theorem squeeze_getElem_prefix (rate : Nat) (h1 : 0 < rate) (h2 : rate ≤ 200) :
    ∀ (i : Nat) (state : 𝔹 200) (a b : Nat) (hia : i < a) (hib : i < b),
      (squeeze state rate a h1 h2)[i]'hia = (squeeze state rate b h1 h2)[i]'hib := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro state a b hia hib
    by_cases hir : i < rate
    · rw [squeeze_getElem_lt state rate a h1 h2 i hir hia,
        squeeze_getElem_lt state rate b h1 h2 i hir hib]
    · rw [not_lt] at hir
      rw [squeeze_getElem_ge state rate a h1 h2 i hir hia,
        squeeze_getElem_ge state rate b h1 h2 i hir hib]
      exact IH (i - rate) (by omega) (KP_bytes state) (a - rate) (b - rate) (by omega) (by omega)

/-- **XOF prefix property.**  Byte `i` of a `turboSHAKE` squeeze is the same regardless
of the total requested length, as long as `i` is in range for both. -/
theorem turboSHAKE_getElem_prefix {mLen : Nat} (rate : Nat) (msg : 𝔹 mLen) (D : Byte)
    (a b i : Nat) (hia : i < a) (hib : i < b) (hrate : 0 < rate ∧ rate ≤ 200) :
    (turboSHAKE rate msg D a hrate)[i]'hia = (turboSHAKE rate msg D b hrate)[i]'hib := by
  unfold turboSHAKE
  exact squeeze_getElem_prefix rate hrate.1 hrate.2 i _ a b hia hib

/-- `turboSHAKE256` prefix property (rate 136). -/
theorem turboSHAKE256_getElem_prefix {n : Nat} (msg : 𝔹 n) (D : Byte) (a b i : Nat)
    (hia : i < a) (hib : i < b) :
    (turboSHAKE256 msg D a)[i]'hia = (turboSHAKE256 msg D b)[i]'hib := by
  unfold turboSHAKE256
  exact turboSHAKE_getElem_prefix 136 msg D a b i hia hib (by omega)

/-! ## One-block absorption

Every Kopis call hashes an input that fits, with its domain-separation byte, strictly inside one
rate-sized block.  For those the sponge collapses: xor the input into a zero state, set the pad
bit, permute once, then squeeze.  The theorem below exposes exactly that, so an implementation can
be matched against `turboSHAKE` without reasoning about the absorb loop at all.

Nothing here changes what is specified — `absorb`, `squeeze` and `turboSHAKE` are untouched; these
are consequences of them. -/

private theorem squeeze_getElem (state : 𝔹 200) (rate rem : Nat) (h1 : 0 < rate)
    (h2 : rate ≤ 200) (i : Nat) (hi : i < rem) :
    (squeeze state rate rem h1 h2)[i]! = (KP_bytes^[i / rate] state)[i % rate]! := by
  induction rem using Nat.strong_induction_on generalizing state i with
  | _ rem IH =>
    rw [squeeze]
    by_cases h : rem ≤ rate
    · rw [dif_pos h, getElem!_pos _ i (by simpa using hi),
        Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Function.iterate_zero_apply, getElem!_pos _ i (by simpa using (by omega : i < 200))]
      simp only [Vector.getElem_ofFn]
    · rw [dif_neg h]
      by_cases hir : i < rate
      · rw [getElem!_pos _ i (by simpa using hi),
          Nat.div_eq_of_lt hir, Nat.mod_eq_of_lt hir, Function.iterate_zero_apply,
          getElem!_pos _ i (by simpa using (by omega : i < 200))]
        simp only [Vector.getElem_cast, Vector.getElem_append, dif_pos hir, Vector.getElem_ofFn]
      · rw [getElem!_pos _ i (by simpa using hi)]
        simp only [Vector.getElem_cast, Vector.getElem_append, dif_neg hir]
        rw [← getElem!_pos _ (i - rate) (by simpa using (by omega : i - rate < rem - rate)),
          IH (rem - rate) (by omega) (KP_bytes state) (i - rate) (by omega)]
        conv_rhs => rw [Nat.div_eq_sub_div h1 (by omega), Nat.mod_eq_sub_mod (by omega),
          Function.iterate_succ_apply]

private theorem absorb_oneBlock (state : 𝔹 200) (input : Array Byte) (rate : Nat)
    (h1 : 0 < rate) (h2 : rate ≤ 200) (hfit : input.size < rate) :
    absorb state input 0 rate h1 h2
      = KP_bytes (((xorBytesAt state input 0 (input.size - 0)).set (rate - 1)
          ((xorBytesAt state input 0 (input.size - 0))[rate - 1]'(by omega) ^^^ (0x80 : Byte))
          (by omega))) := by
  rw [absorb, dif_neg (by omega)]

set_option maxRecDepth 8000 in
/-- **One-block `turboSHAKE`.**  When the message and its domain-separation byte fit strictly
inside one rate-sized block, byte `i` of the output is byte `i % rate` of the start state permuted
`i / rate + 1` times, where the start state is the block laid into a zero state with the `0x80`
pad bit set.

The start state is a parameter, characterised pointwise, so a caller can supply whatever
description of the padded block it already has. -/
theorem turboSHAKE_oneBlock_getElem {mLen : Nat} (rate : Nat) (msg : 𝔹 mLen) (D : Byte)
    (outLen : Nat) (hrate : 0 < rate ∧ rate ≤ 200) (hfit : mLen + 1 < rate)
    (st : 𝔹 200)
    (hst : ∀ j < 200, st[j]! =
        if j < mLen then msg[j]!
        else if j = mLen then D
        else if j = rate - 1 then (0x80 : Byte)
        else 0)
    (i : Nat) (hi : i < outLen) :
    (turboSHAKE rate msg D outLen hrate)[i]!
      = (KP_bytes^[i / rate + 1] st)[i % rate]! := by
  unfold turboSHAKE
  have hsz : (msg.toArray.push D).size = mLen + 1 := by simp
  have hstate :
      (xorBytesAt (Vector.replicate 200 (0 : Byte)) (msg.toArray.push D) 0
          ((msg.toArray.push D).size - 0)).set (rate - 1)
        ((xorBytesAt (Vector.replicate 200 (0 : Byte)) (msg.toArray.push D) 0
            ((msg.toArray.push D).size - 0))[rate - 1]'(by omega) ^^^ (0x80 : Byte))
        (by omega) = st := by
    apply Vector.ext
    intro j hj
    rw [Vector.getElem_set, ← getElem!_pos st j hj, hst j hj]
    by_cases hlast : rate - 1 = j
    · rw [if_pos hlast, ← hlast]
      simp only [xorBytesAt, Vector.getElem_ofFn, hsz, Nat.sub_zero,
        if_neg (show ¬(rate - 1 < mLen + 1) by omega)]
      rw [if_neg (by omega), if_neg (by omega)]
      simp
    · rw [if_neg hlast]
      simp only [xorBytesAt, Vector.getElem_ofFn, hsz, Nat.sub_zero]
      by_cases hjm : j < mLen + 1
      · rw [if_pos hjm, dif_pos (by omega)]
        by_cases hjm2 : j < mLen
        · rw [if_pos hjm2, Array.getElem_push, dif_pos (by simpa using hjm2)]
          simp [getElem!_pos msg j hjm2]
        · rw [if_neg hjm2, if_pos (by omega), Array.getElem_push,
            dif_neg (by simpa using hjm2)]
          simp
      · rw [if_neg hjm, if_neg (by omega), if_neg (by omega), if_neg (fun h => hlast h.symm)]
        simp
  rw [squeeze_getElem _ _ _ hrate.1 hrate.2 i hi,
    absorb_oneBlock _ _ _ hrate.1 hrate.2 (by rw [hsz]; omega), hstate,
    ← Function.iterate_succ_apply]

end Spec.TurboSHAKE
