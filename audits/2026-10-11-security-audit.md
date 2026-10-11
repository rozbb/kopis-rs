# Kopis (kopis-rs) Cryptographic Security Assessment

| | |
|---|---|
| **Target** | `kopis` crate, Rust, `no_std`; serial, AVX2 and NEON backends; Lean 4 / Aeneas correctness proofs |
| **Commit** | `2aec76bc4a1e77fd431c9cf3a9d8ecc2e7caa622` (branch `main`) |
| **Date** | 2026-10-11 |
| **Toolchain used for testing** | rustc 1.98.1 (stable), x86-64 host with AVX2; valgrind 3.24.0; qemu-system-aarch64 10.0.13 (`-cpu max`, bare metal) |
| **Prior report** | `audits/2026-07-30-fable5.md` (commit `5bcc4e5`); status of each prior finding is given in Section 6 |

---

## 1. Scope, Methodology and Limitations

### 1.1 Scope

In scope:

* All of `src/`: `lib.rs`, `kem.rs`, `pke.rs`, `sample.rs`, `ser.rs`, `impls.rs`, `consts.rs`, `arithmetic/` (`plain_arith.rs`, `ntt_arith.rs`, `ntt_crt.rs`), `backend/avx2/*`, `backend/neon/*`.
* `build.rs`, `Cargo.toml`, `Cargo.lock`, and the normal (shipped) dependency graph: `turboshake 0.7.1` (with `keccak 0.2.1`, `sponge-cursor 0.1.0`), `subtle 2.6.1`, `zeroize 1.9.0`, `rand_core 0.9.5`, `cpufeatures 0.3.0`.
* `tests/`, `benches/`, `ct-check/`, `ct-check.sh`, `.github/workflows/ci.yml`, `README.md`.
* The specification `lean/kopis-spec.md` and its Lean rendering in `lean/Spec/`.
* The Lean assurance argument: `lean/TopLevelTheoremsSerial.lean` (and its generated AVX2/NEON twins), `lean/TrustBase.lean`, `lean/Kopis/Avx2/Intrinsics.lean`, `lean/Kopis/Neon/Intrinsics.lean`, and the files that hold the trusted `axiom` declarations.

Out of scope: the untracked files in the working tree. The Lean proofs were read but **not rebuilt** (another party was concurrently editing and building them); statements about what the proofs establish are based on reading the theorem statements, the axiom-audit gate, and the CI configuration that runs it.

### 1.2 Methodology

* Manual line-by-line review of the protocol layer (FO transform, implicit rejection, domain separation, sampling, rounding, serialization) against `lean/kopis-spec.md`.
* Exact arithmetic bound analysis of the two-prime NTT (q1 = 7681, q2 = 10753) and CRT reconstruction in all three backends. This combined exhaustive enumeration over the full input domain wherever it is feasible (Barrett reduction over all 2^16 inputs; Montgomery multiplication over all 2^16 inputs times every twiddle and its negation; the i32 Montgomery reduction over the entire reachable accumulator range; Garner/CRT over all 82,593,793 residue pairs on NEON) with per-coefficient interval propagation through every butterfly using the actual twiddle values.
* Constant-time review: source inspection of every operation on secret data, plus dynamic taint checking (the project's own Valgrind harness, re-run under several build configurations) and disassembly of the AArch64 build.
* Memory-safety review of every `unsafe` block, including release-mode integer wrapping in the bounds checks.
* Empirical tests and demonstrations. Every test program lives under `/tmp/claude-1000/-home-dev-kopis-rs/95d96172-9eba-44ec-ad2e-c38a589cee16/scratchpad/audit/`; the repository itself was not modified apart from adding this report. They comprise:
  * `numcheck/`: arithmetic bounds;
  * `residue/`: stack residue of secrets;
  * `crate-ovf/`: the wrapping bounds-check demonstration;
  * `ctcheck/`: the ct-check re-runs;
  * `neon/`: the NEON bare-metal qemu harness, its bounds model and disassembly classification.
* Test-suite execution. `cargo test --release` passes in three configurations:
  * autodetect (25 unit, 3 KAT, 2 TurboSHAKE, 1 doctest);
  * `--cfg kopis_backend="serial"` (17 unit + same);
  * forced AVX2 (25 unit + same).

  On AArch64, the NEON backend was exercised under qemu-system-aarch64 (`-cpu max`), including all 75 KAT vectors and a bit-exact regeneration of `tests/neon_intrinsics_vectors.jsonl`.

### 1.3 Limitations

* No AArch64 hardware was available. NEON results come from qemu TCG emulation and from static disassembly. Timing on real microarchitectures was not measured on any platform: constant-time claims below concern control flow, memory addressing and instruction selection only.
* Lean proofs were not re-checked by the assessor. The audit-gate logic and its CI wiring were reviewed instead.
* `cargo audit` / `cargo deny` were not available offline, so no advisory-database check was performed.
* The security of the Kopis design itself (a Saber-parameterised Module-LWR KEM with an ML-KEM-style FO transform) was not re-analysed. Parameter sets were confirmed to coincide with LightSaber, Saber and FireSaber.

---

## 2. Executive Summary

The implementation is in good shape. We found no issue that lets an attacker recover keys, forge shared secrets, cause a decapsulation mismatch, or trigger memory corruption through the public API.

**Specification conformance.** The FO transform, implicit rejection, domain separators, rounding constants (h1 = 4, h2 = 2^8 - 2^(9-t) + 4), CBD bit layout, LSB-first serialization, key-generation XOF layout and all object sizes match `lean/kopis-spec.md` exactly in all three backends.

**Arithmetic.** The two-prime NTT arithmetic is exact for every input the crate can produce or accept:
* the worst forward-transform lane is 30,674 of 32,767 for AVX2 and 31,430 for NEON;
* the CRT window holds the worst-case product 25,162,752 inside the 41,296,896 half-range.

**Constant-time behaviour.** No secret-dependent branch, secret-indexed memory access or variable-time instruction was found in any backend. The project's Valgrind harness passes on serial and AVX2, including the default x86-64 baseline build that CI does not check.

**Input validation.** All byte strings of the correct length are valid public keys and ciphertexts, because the moduli are powers of two. No input validation is therefore required, and none is missing.

**Formal verification.** The Lean development proves that, for every seed, randomness, public-key byte string and ciphertext byte string, the extracted code of each backend terminates without panic and returns exactly what the Lean specification returns. It does this with no `sorry`, behind an enforced axiom whitelist that runs in CI. This is a strong functional-correctness result. It says nothing about side channels, secret erasure, or IND-CCA security, and it trusts:
* the `turboshake` crate (for all KEM-level hashing);
* 96 hand-written intrinsic axioms;
* for AVX2, the Lean compiler (through `bv_decide`).

**Most significant findings.** All are hardening or assurance issues:
* intermediate secrets (including the decrypted FO message) survive on the stack after every operation, which was demonstrated empirically;
* the bounds checks that guard the `unsafe` SIMD loads wrap in release builds, which was demonstrated to permit an out-of-bounds read, although no caller can reach it;
* there are several gaps between the configurations that are checked (by Valgrind and by Lean) and the configuration that actually ships by default;
* CI supply-chain hygiene.

**No finding is rated Critical, High or Medium.**

### 2.1 Findings by severity

| Severity | Count |
|---|---|
| Critical | 0 |
| High | 0 |
| Medium | 0 |
| Low | 8 |
| Informational | 10 |

| ID | Title | Severity |
|---|---|---|
| OPUS55-KOPIS-001 | Intermediate secrets (FO message, secret seed, CBD bytes, sponge states) are not erased | Low |
| OPUS55-KOPIS-002 | Bounds checks guarding `unsafe` SIMD loads/stores wrap in release builds | Low |
| OPUS55-KOPIS-003 | Backend selection can be forced past the build-script checks (host-CPU AVX2 acceptance, raw `kopis_*` cfgs) | Low |
| OPUS55-KOPIS-004 | The shipped default x86-64 configuration is not the one that is taint-checked in CI or extracted to Lean | Low |
| OPUS55-KOPIS-005 | Instruction-scan coverage defects in `ct-check` | Low |
| OPUS55-KOPIS-006 | AVX2 proof trust base includes native `bv_decide` axioms (Lean compiler trusted) | Low |
| OPUS55-KOPIS-007 | `encapsulate_deterministic` is part of the stable public API | Low |
| OPUS55-KOPIS-008 | CI supply-chain hygiene: unpinned actions, default token permissions, `curl \| sh`, unlocked builds | Low |
| OPUS55-KOPIS-009 | Constant-time behaviour holds only for optimised builds, and only under a fixed-latency-multiplier assumption | Informational |
| OPUS55-KOPIS-010 | AVX2 CBD contract admits μ ∈ {12}, for which it silently returns wrong coefficients | Informational |
| OPUS55-KOPIS-011 | Load-bearing arithmetic and safety comments are stale or wrong (code is correct) | Informational |
| OPUS55-KOPIS-012 | Inner-dimension bound that guarantees CRT exactness is `debug_assert!` only | Informational |
| OPUS55-KOPIS-013 | Secret-carrying internal types derive `Debug`, `PartialEq` and `Copy` | Informational |
| OPUS55-KOPIS-014 | KAT harness weaknesses and self-referential vector provenance | Informational |
| OPUS55-KOPIS-015 | Lean trust-base precision: over-general hash axioms, untested memory axioms, implicit little-endianness | Informational |
| OPUS55-KOPIS-016 | The secret-key accessor `as_bytes()` is undocumented | Informational |
| OPUS55-KOPIS-017 | Dependency and metadata hygiene (`turboshake` range pin, dead cfg, licence string, README CI skip) | Informational |
| OPUS55-KOPIS-018 | No data-independent-timing mode is enabled on AArch64 (PSTATE.DIT) | Informational |

---

## 3. Background: Scheme Summary as Implemented

Kopis is Saber's Module-LWR PKE: q = 2^13, p = 2^10, T = 2^t, over R = Z[X]/(X^256+1). It is wrapped in an ML-KEM-style FO⊥̸ transform with implicit rejection and instantiated with TurboSHAKE (RFC 9861).

| Set | ℓ | μ | t | pk bytes | ct bytes | Matches |
|---|---|---|---|---|---|---|
| Kopis-512 | 2 | 10 | 3 | 672 | 736 | LightSaber |
| Kopis-768 | 3 | 8 | 4 | 992 | 1088 | Saber |
| Kopis-1024 | 4 | 6 | 6 | 1312 | 1472 | FireSaber |

Key implementation choices that matter for security:

* **The secret key is the 32-byte seed** (`src/kem.rs:68-78`). The expanded form, consisting of the NTT-domain secret, z, the public key and its hash, is cached in `KemSecretKey` and recomputed from the seed on import. As a result there is no "decapsulation key consistency" check to get wrong.
* **Ring products** are computed exactly over the integers by a negacyclic NTT modulo two 16-bit primes and Garner reconstruction (`src/arithmetic/ntt_crt.rs`). The results are then reduced mod 2^16 by truncation. All later shifts and masks consume only the low 13 (or 10) bits.
* **No rejection sampling.** Matrix generation unpacks 13-bit fields from TurboSHAKE128 output (`src/sample.rs:123-161`), so key generation and encapsulation have no data-dependent loop counts.

---

## 4. Findings

### OPUS55-KOPIS-001: Intermediate secrets are not erased

| | |
|---|---|
| **Severity** | Low |
| **Impact** | Secret material that determines the shared secret or the long-term key remains in freed stack memory after every API call, and so becomes available to any later memory-disclosure primitive (an over-read in co-resident code, a core dump, swap, cold boot). |
| **Exploitability** | High difficulty. It requires an independent memory-disclosure capability in the same process. |
| **Locations** | `src/kem.rs:125-126` (`k`, `r` in encapsulation); `src/kem.rs:153-179` (`randomness` = decrypted FO message, `k`, `rprime`, `buf` = re-encryption, `reject_val`); `src/pke.rs:139` (`secret_seed`); `src/pke.rs:153` (`vec_s`, coefficient-domain secret); `src/pke.rs:201-210` (`v`, `mprime`, `m` in decryption); `src/pke.rs:225-226` (`vec_sprime`, `sprime_ntt`); `src/sample.rs:103` (`backing_buf`, the raw CBD bytes); `src/backend/avx2/sample.rs:177`, `src/backend/neon/sample.rs:169` (`bufs`); `src/backend/avx2/keccak.rs:252-261`, `src/backend/neon/keccak.rs:229-238` (padded blocks holding the seed and the sponge state); `Cargo.toml:12` (`turboshake` without its `zeroize` feature) |

**Description.**

The crate's stated policy is visible in two places:
* `ZeroizeOnDrop` on `KemSecretKey`, `PkeSecretKey` and `SharedSecret`;
* explicit `zeroize()` of the RNG output at `src/kem.rs:103` and `src/impls.rs:90`.

That policy covers only the long-lived containers. The transient values listed above are dropped without being wiped. The most sensitive of them are:

* **The decrypted FO message `randomness` in `decap`.** Together with the public key hash it determines the session key k. That holds even when decapsulation rejects, if the decryption was correct.
* **The secret seed `secret_seed` and the CBD bytes.** They determine `s`.

Separately, `turboshake` is pulled in with `default-features = false`. That disables its `zeroize` feature, so the hasher and reader states (`turboshake-0.7.1/src/lib.rs:137-149, 181-189`) that absorbed `sk`, `z`, or the FO message are never cleared on drop.

**Evidence.** The harness `residue/src/main.rs` uses only the public API. After each call returns, it scans 256 KiB of dead stack below the caller's frame for known byte patterns. Results for Kopis-768 with the default build, which are identical under `--cfg kopis_backend="serial"`:

```
after keygen: secret_seed occurrences in dead stack = 2
after encap: m occurrences = 1, ss occurrences = 2
after decap: m occurrences = 1, k occurrences = 3
after rejected decap (c[0]^=1): m occurrences = 1
```

Before each decapsulation the stack was overwritten with zeros, so the hits come from the decapsulation itself. In the last line, a ciphertext with one bit flipped is still rejected, yet it leaves the original message m, and with it the honest session key, on the stack.

**Recommendation.**
* Wrap the listed locals in `zeroize::Zeroizing` or call `.zeroize()` before return.
* Enable `turboshake`'s `zeroize` feature.
* Document the policy and its limits. In particular:
  * values moved out by return (`SharedSecret`, `KemSecretKey`) leave copies that no drop-based scheme can reach;
  * register spills cannot be erased from Rust.
* If stronger guarantees are required, consider a stack-bleaching wrapper at the public entry points.

---

### OPUS55-KOPIS-002: Bounds checks guarding `unsafe` SIMD loads/stores wrap in release builds

| | |
|---|---|
| **Severity** | Low |
| **Impact** | The memory-safety argument for every `unsafe` block in the crate is false as stated. A future caller that passes a large index or offset would get an out-of-bounds read or write in release builds, with no panic. |
| **Exploitability** | Not reachable today. Every caller uses compile-time-bounded indices: vector index ≤ 63, byte offsets ≤ 416. The Lean proofs independently establish that the asserts never fire on the paths they cover. |
| **Locations** | `src/backend/avx2/intrinsics.rs:373, 382, 391, 400, 409, 418, 427, 439, 452, 461`; `src/backend/neon/intrinsics.rs:501, 510, 519, 528, 537, 546, 560, 572`; the safety claims at `src/backend/avx2/intrinsics.rs:28-30` and `src/backend/neon/intrinsics.rs:40-42` |

**Description.**

Each accessor is a safe `pub(crate) fn` that checks its argument and then performs an unchecked unaligned load or store. For example, `src/backend/avx2/intrinsics.rs:372-376`:

```rust
pub(crate) fn load_i16<const N: usize>(src: &[i16; N], i: usize) -> Vec256 {
    assert!(16 * (i + 1) <= N);
    Vec256(unsafe { _mm256_loadu_si256(src.as_ptr().add(16 * i).cast()) })
}
```

The module documentation says the check "makes the access in-range for *any* arguments". That is true only with overflow checks enabled, and the release profile disables them:
* for `i = usize::MAX / 16`, `16 * (i + 1)` wraps to 0 and the assertion passes;
* for `load_u8x16`, `offset = usize::MAX - 15` makes `offset + 16` wrap to 0. The pointer then lands 16 bytes *before* `src`.

**Evidence.**
* **AVX2.** `crate-ovf/` adds a test to a copy of the crate and runs it with `RUSTFLAGS='-C target-feature=+avx2 --cfg kopis_backend="avx2"' cargo test --release`:

  ```
  i = 0xfffffffffffffff: 16*(i+1) evaluates to 0, assert(16*(i+1) <= 16) = true
  offset = 0xfffffffffffffff0: offset+16 evaluates to 0, assert passes = true
  load_u8x16(&[0u8;16], usize::MAX-15) panicked? false
  ```

  The load executed and read the 16 bytes preceding the array.
* **NEON.** The same behaviour was shown under qemu. `load_i16(&[i16; 8], usize::MAX)` returned guard words planted immediately before the array.

**Recommendation.** Write the checks so that they cannot overflow:
* `assert!(i < N / 16)`, or equivalently `i <= N / 16 - 1` guarded against N < 16;
* `assert!(offset <= src.len().saturating_sub(16) && src.len() >= 16)`;
* or obtain the bytes through `src.get(offset..offset + 16)`, which already handles overflow, and load from the resulting sub-slice.

---

### OPUS55-KOPIS-003: Backend selection can be forced past the build-script checks

| | |
|---|---|
| **Severity** | Low |
| **Impact** | The result is a binary that executes AVX2 or FEAT_SHA3 instructions unconditionally on CPUs that lack them. That is a SIGILL in practice, and undefined behaviour by Rust's target-feature rules. |
| **Exploitability** | Requires a build-time misconfiguration by the integrator. No attacker control. |
| **Locations** | `build.rs:70-79`, `build.rs:201-214` (`avx2_is_available`); `src/backend/avx2/cpu.rs:20-22`; `build.rs:104-109`; `src/backend/neon/cpu.rs` |

**Description.**

1. **AVX2, prior finding M1, unchanged.** `--cfg kopis_backend="avx2"` is accepted without `-C target-feature=+avx2` whenever the build is not a cross-compile and the *build host* has AVX2 (`build.rs:208-213`). `kopis_avx2_assume` then folds `available()` to `true` (`cpu.rs:21`). An image built on an AVX2 CI runner and deployed to an older VM executes AVX2 with no CPUID check.
2. **Raw cfgs bypass the build script.** `RUSTFLAGS='--cfg kopis_neon'` (or `kopis_avx2_assume`) is not filtered. On `aarch64-unknown-none` without `+sha3` this compiles the NEON backend, which emits `eor3`/`rax1`/`xar`/`bcax` with no guard. It also compiles for `aarch64-unknown-none-softfloat`, with only rustc's "unsound" warnings. The documented `kopis_backend="neon"` path does check correctly, and panics at `build.rs:85`.
3. **Documentation.** `build.rs:11` says "Either way the resulting binary runs everywhere for its architecture". A `+sha3` AArch64 build, which is the only configuration in which NEON is used, faults on Cortex-A72, Cortex-A76 and Neoverse-N1. This was shown under qemu, where the first fault occurred in the `keccak` dependency, which also keys on `+sha3`.

**Recommendation.**
* In forced mode, require `avx2` in `CARGO_CFG_TARGET_FEATURE`. Do not treat host detection as sufficient; at most, downgrade it to the runtime-checked backend.
* In `build.rs`, panic if `kopis_avx2`, `kopis_avx2_assume` or `kopis_neon` appear in the incoming rustflags. Alternatively, rename them to something clearly internal.
* Correct the portability claim.

---

### OPUS55-KOPIS-004: The shipped default x86-64 configuration is not the one checked in CI or extracted to Lean

| | |
|---|---|
| **Severity** | Low |
| **Impact** | The two strongest assurance mechanisms, Valgrind taint checking and the Lean correspondence proof, are applied to builds that differ from what a downstream `cargo build` on x86-64 produces. No defect was found in the gap, but it is closed only by an informal argument. |
| **Exploitability** | Not directly exploitable. This is an assurance gap. |
| **Locations** | `ct-check.sh:119-123` (`MARCH="-C target-cpu=x86-64-v3"`); `ct-check/scan-instrs.py:129`; `extract_rust_to_lean.sh:50`; `build.rs:104-106`; `src/backend/avx2/cpu.rs:20-22`; `lean/Kopis/Avx2/Intrinsics.lean:85` |

**Description.**

A downstream x86-64 consumer gets baseline x86-64 codegen, with AVX2 entered through `#[target_feature]` functions behind a `cpufeatures` CPUID probe. Neither checking mechanism sees that build:

* **Constant-time checking.** `ct-check.sh` always forces `-C target-cpu=x86-64-v3`, and the CI job runs only `--backend serial` and `--backend avx2` (`.github/workflows/ci.yml:110-113`). The baseline build, with the runtime dispatch and the baseline-ISA code generated for the serial fallback and for glue code, is never checked.
* **Lean.** The AVX2 extraction is produced with `--cfg kopis_backend="avx2" -C target-feature=+avx2`. As a result `available()` extracts as `ok true` (`lean/ExtractedRustAvx2.lean:1572-1573`). Correctness of the shipped default therefore rests on a composition argument: the AVX2 branch matches the AVX2 extraction, and the fallback matches the serial extraction. The CPUID probe that justifies the `unsafe` calls is unverified. The axiom `Kopis.Avx2.available_ok` is consequently redundant, since it is provable by `rfl`, and its docstring calling `cpu.rs` "extracted opaquely" is inaccurate.

**Evidence.**
* We re-ran Valgrind on a copy of `ct-check.sh` with `MARCH=""`, in both native (runtime dispatch) and serial configurations: **0 errors**.
* Callgrind confirmed that `avx2::keccak::permute` and `avx2::ntt::*` execute under Valgrind, so the dispatched AVX2 path was covered.
* The gap is therefore one of process, not a present leak.

**Recommendation.**
* Add a CI leg `./ct-check.sh --backend native` with `MARCH` empty.
* Either remove `available_ok` and correct its documentation, or extract the default configuration as a fourth target.

---

### OPUS55-KOPIS-005: Instruction-scan coverage defects in `ct-check`

| | |
|---|---|
| **Severity** | Low |
| **Impact** | The scan's documented safety net does not work as described, and stale allowlist entries could later mask new variable-time instructions. |
| **Exploitability** | Not exploitable in itself. |
| **Locations** | `ct-check/scan-instrs.py:181`; `ct-check/scan-instrs.py:17-18`; `ct-check/probe/src/lib.rs:4-7`; `ct-check/instr-allowlist.txt:17, 18, 23`; `ct-check.sh:194` |

**Description.**

1. **The probe rlib is never scanned.** `scan-instrs.py:181` filters cargo artefacts on the target names `("kopis", "ct-scan-probe")`, but cargo reports the library target as `ct_scan_probe`. Only `libkopis-*.rlib` is disassembled. The probe exists precisely to force monomorphisation of KEM code; the stated rationale ("libkopis.rlib … holds no instantiated KEM code") is false, and the probe's instructions are skipped. The impact today is small, because the non-generic aliases in `impls.rs` cause the KEM code to be emitted into `libkopis` (29k instructions scanned).
2. **Stale allowlist.** Entries naming `avx2/neon::ser::deserialize` and `arithmetic::ring_arith::RingElem` match nothing; there is no `ring_arith` module. The scanner does not report unused entries, and matching is by substring of demangled symbols, so a stale entry can silently cover future code.
3. **Weak self-test oracle.** The self-test treats any non-zero Valgrind exit as "leak detected" (`ct-check.sh:194`), so a crash or a SIGILL would also pass it.
4. **NEON is not dynamically checked.** NEON has no dynamic check at all; only the instruction scan covers it.
5. **Division helpers are not flagged.** Calls to `__udivti3` or `__aeabi_uldivmod` are not flagged, and dependency rlibs are not scanned. None are present today.

**Evidence.**
* `./ct-check.sh --selftest` and full runs pass. The scan counts were: host/serial 29,069; host/avx2 27,355; aarch64/serial 109,738; aarch64/neon 53,087; thumbv7em 47,386 instructions.
* The only hits are `div` in `sponge-cursor` absorb/squeeze helpers, whose operands are lengths derived from the public sponge rate.

**Recommendation.**
* Compare against `ct_scan_probe`.
* Fail on unused allowlist entries.
* Grep for the two expected Valgrind error kinds in the self-test.
* Add division-libcall symbols to the matchers.
* Consider an arm64 Linux runner for Valgrind.

---

### OPUS55-KOPIS-006: AVX2 proof trust base includes native `bv_decide` axioms

| | |
|---|---|
| **Severity** | Low |
| **Impact** | The AVX2 top-level theorems depend on four `Lean.ofReduceBool`-style axioms produced by `bv_decide`. That places the Lean compiler, the native runtime and the LRAT checker run natively in the trusted computing base for the AVX2 correctness claim. |
| **Exploitability** | Assurance only. |
| **Locations** | `lean/TrustBase.lean:188-191`; `lean/Kopis/Avx2/NttMulLane.lean:53`; `lean/Kopis/Avx2/Reduce.lean:33, 37, 455` |

**Description.**

The four lemmas are trivial bit-vector identities. Two examples are `(x <<< 16).sshiftRight 16 = (extractLsb' 0 16 x).signExtend 32` and `v &&& 0xFFFF#32 = setWidth 32 (setWidth 16 v)`. The NEON stack proves the equivalent facts bit by bit (`lean/Kopis/Neon/Reduce.lean:1106-1107`), so its footprint is kernel-only. Five further `bv_decide` uses (`Reduce.lean:40, 357, 358, 452, 453`) are not in the top-level footprint today.

The comment at `TrustBase.lean:54-56` ("receipt validated by a Lean program") understates the dependency: that validator itself runs natively.

**Recommendation.** Replace the four lemmas with kernel proofs, using `BitVec.eq_of_getLsbD_eq` with `decide +kernel` per bit, as was done for NEON. Then remove them from the whitelist.

---

### OPUS55-KOPIS-007: `encapsulate_deterministic` is part of the stable public API

| | |
|---|---|
| **Severity** | Low |
| **Impact** | A caller who supplies non-uniform or repeated `randomness` breaks the scheme's security completely. The FO message is that input verbatim (`src/kem.rs:129-138`), so reusing it reproduces the same `(ct, k)` pair, and low-entropy values make k guessable by anyone holding the public key. |
| **Exploitability** | Requires API misuse by an integrator. |
| **Locations** | `src/impls.rs:94-109` |

**Description.**

The function exists for KAT testing (its documentation says so). It is nonetheless exported on every public-key type, with the same visibility as `encapsulate_with_rng`. The spec makes uniform sampling a MUST (`lean/kopis-spec.md:48`), but the type system does not enforce it.

**Recommendation.** Gate the function behind an opt-in Cargo feature (for example `deterministic` or `hazmat`) or mark it `#[doc(hidden)]`. Rename it so that the hazard is visible at the call site.

---

### OPUS55-KOPIS-008: CI supply-chain hygiene

| | |
|---|---|
| **Severity** | Low |
| **Impact** | A compromised third-party action or install script runs with the repository token and can tamper with CI results, including the axiom-audit and extraction-currency gates on which the assurance argument relies. |
| **Exploitability** | Requires compromise of an upstream action, the elan script host, or a git dev-dependency. |
| **Locations** | `.github/workflows/ci.yml:40-41, 56-57, 81, 94-95, 121-122, 125, 132, 154, 157-158, 165, 219`; `Cargo.toml:47-57`; `extract_rust_to_lean.sh:24-31` |

**Description.**
* Actions are referenced by mutable tag: `actions/checkout@v3` (also deprecated, Node 16), `dtolnay/rust-toolchain@stable` / `@master`, and `actions/cache@v4`.
* There is no top-level `permissions:` block.
* elan is installed by piping `raw.githubusercontent.com/.../master/elan-init.sh` into `sh`.
* Aeneas and Charon binaries are fetched with `curl | tar` without checksum verification.
* `cargo test` runs without `--locked`, and it builds git dev-dependencies (a personal fork of `aws-lc-rs` on a branch, and `mlkem-selkie`) whose build scripts execute in CI.
* There is no `cargo audit` or `cargo deny` step.

The shipped library is not affected. `cargo tree -e normal` contains only registry crates, and `[patch]` entries do not propagate to dependants.

**Recommendation.**
* Pin all actions by commit SHA.
* Declare `permissions: contents: read`.
* Pin and checksum the elan and Aeneas downloads.
* Use `--locked`.
* Add `cargo deny check advisories sources`.

---

### OPUS55-KOPIS-009: Constant-time behaviour holds only for optimised builds and fixed-latency multipliers

| | |
|---|---|
| **Severity** | Informational |
| **Locations** | `src/kem.rs:182-183`; `subtle-2.6.1/src/lib.rs:239, 524`; `README.md` "Checking for constant-timeness" |

**Description.**
* **Debug builds branch on secrets.** A debug (`opt-level=0`, overflow-checked) build of the ct-check harness produced 20,370 Valgrind errors from seven contexts, all inside `subtle`: the `debug_assert!` in `From<u8> for Choice` and the overflow-checked negation in `conditional_assign`, both reached from the FO select at `kem.rs:182-183`. No error was attributed to kopis code. Release builds are clean.
* **The portable backend assumes constant-time multiplication.** The portable backend relies on constant-time 16×16 and 32×32 multiplication. That assumption fails on some cores that `no_std` users target; certain Cortex-M0/M3-class cores have early-terminating multipliers. The README mentions Cortex-M3, but the note is attached to the instruction scan rather than to the scheme.

**Recommendation.** State explicitly that the constant-time guarantee is for optimised builds on cores with fixed-latency multipliers.

---

### OPUS55-KOPIS-010: AVX2 CBD contract admits μ = 12

| | |
|---|---|
| **Severity** | Informational (prior L2, unchanged) |
| **Locations** | `src/backend/avx2/sample.rs:38, 70` |

**Description.** `popcount_small` is correct only for values below 32. That means μ/2 ≤ 5, so μ ≤ 10. The contract nevertheless reads "`MU` must be even and in `2..=13`". With μ = 12, bit 5 of each half is dropped and the sampled distribution is wrong, and no assertion fires. The bug is unreachable with the current parameter sets.

**Recommendation.** Add `const { assert!(MU <= 10 && MU % 2 == 0) }` to the function.

---

### OPUS55-KOPIS-011: Stale or wrong load-bearing comments

| | |
|---|---|
| **Severity** | Informational |
| **Locations** | `src/arithmetic/ntt_arith.rs:39, 113-117`; `src/backend/neon/ntt.rs:499-501, 776`; `src/backend/neon/intrinsics.rs:210-211`; `src/backend/avx2/mod.rs:14-15`; `build.rs:11` |

**Description.** The code is correct in every case below; only the stated reasoning is wrong.

* **`ntt_arith.rs:113-117` describes the retired single-prime design.** It refers to an "i64 accumulator", "(p/2 + 41)²", "< 2^52" and "2^31 · p". The correct statement is as follows:
  * the accumulator is `[i32; 512]`;
  * each lane is bounded by 4·(q₂/2)² = 115,605,504 < 2^31, which we verified exhaustively;
  * Montgomery reduction over that range yields |r| ≤ 7,140 (q₂) and 4,740 (q₁).
* **`ntt_arith.rs:39` gives "|·| ≤ q/2 + 41".** The bound is exactly q/2: Barrett reduction over all 2^16 inputs yields at most 3,840 and 5,376.
* **`neon/ntt.rs:499-501` states the inverse transform requires only |a| < q.** For q₂ that is insufficient: two Gentleman-Sande levels from 10,752 reach 43,008 and overflow. The true requirement is |a| ≤ 8,191, and the actual input is ≤ 7,141.
* **The `ushl` documentation claims counts of ±16 give zero.** The hardware uses the signed low byte, so 0x0100 shifts by 0. The Lean model and the recorded vectors are correct, and callers only pass −7..0.
* **`avx2/mod.rs:14-15` locates `unsafe` in the wrong modules.** It says `unsafe` exists in `keccak` and `cpu`; it exists in neither (outside tests).

**Evidence (forward-NTT interval propagation with the actual twiddles, `numcheck/`).**

| Prime | Serial (3,3,2) | AVX2 (3,4,1) | Runs (4,4) | Limit |
|---|---|---|---|---|
| q₁ | 16,650 | 21,171 | 21,220 | 32,767 |
| q₂ | 23,624 | 30,674 | 30,683 | 32,767 |

* Inverse transforms peak at 18,962 (q₁) and 28,562 (q₂). The final scale leaves |r| ≤ 4,289 < q₁ and 6,209 < q₂, so CRT canonicalisation is valid.
* The AVX2 module documentation (`src/backend/avx2/ntt.rs:27-35`) now states the table-dependent 30,700 bound. That resolves prior finding M2.

**Recommendation.** Correct the comments above. Add an inverse-transform growth test that mirrors the forward one.

---

### OPUS55-KOPIS-012: Inner-dimension bound for CRT exactness is `debug_assert!` only

| | |
|---|---|
| **Severity** | Informational (prior L4, partially fixed) |
| **Locations** | `src/arithmetic/ntt_arith.rs:185, 204` |

**Description.** The CRT reconstruction is exact only while ℓ·256·8191·(μ/2) < 41,296,896. Today's worst case is 25,162,752. The inner-dimension check that protects this bound is debug-only, so a future parameter set with ℓ·μ/2 ≥ 20 would silently compute wrong products in release builds. Prior finding L4 also covered `Matrix::deserialize_10`; that function now uses `assert_eq!`, which is fixed.

**Recommendation.** Use a `const` assertion on `L * MU / 2`.

---

### OPUS55-KOPIS-013: Secret-carrying internal types derive `Debug`, `PartialEq` and `Copy`

| | |
|---|---|
| **Severity** | Informational (prior L9, unchanged) |
| **Locations** | `src/arithmetic/plain_arith.rs:17, 155`; `src/arithmetic/ntt_arith.rs:40` |

**Description.**
* `RingElem` and `Matrix`, which hold `s` and `s'`, derive `Debug` and a short-circuiting `PartialEq`.
* `RingElem` and `NttElem` are also `Copy`, which multiplies unerasable copies of the secret (see OPUS55-KOPIS-001).

All of these types are crate-internal.

**Recommendation.** Derive `Debug` and `PartialEq` only under `#[cfg(test)]`, and drop `Copy` where it is practical.

---

### OPUS55-KOPIS-014: KAT harness weaknesses and self-referential vector provenance

| | |
|---|---|
| **Severity** | Informational |
| **Locations** | `tests/known_answer_tests.rs:73-80`; `tests/test_vectors-kopis*.jsonl`; `tests/turboshake_vectors.rs:79-90` |

**Description.**
* **No minimum-count check (prior L5, unchanged).** `kat_test!` iterates over whatever it parses, so an empty or truncated file passes vacuously.
* **Vector composition.** Each file holds 25 vectors: 11 marked `malformed` (wrong lengths), 6 valid mauled ciphertexts that exercise implicit rejection, and 8 honest.
* **Provenance is not recorded.** The commits say only "Copy over new test vectors". The KATs are consumed by both the Rust tests and the Lean spec runner, so they demonstrate agreement between the Rust code and the Lean spec, not between independent implementations.
* **The TurboSHAKE vectors are generated by the crate under test.** They come from the same `turboshake` crate whose correctness the serial proof assumes, anchored by only four RFC 9861 vectors.
* **Running the test suite rewrites a committed file.** `cargo test` runs `generate`, which overwrites `tests/turboshake_vectors.jsonl`.

**Recommendation.**
* Assert a minimum number of executed vectors.
* Record the generator and commit hash for the KATs.
* Make vector regeneration opt-in via an environment variable, as the intrinsic-vector tests already are.
* Anchor the TurboSHAKE spec on the full RFC 9861 test set, including long-message vectors.

---

### OPUS55-KOPIS-015: Lean trust-base precision

| | |
|---|---|
| **Severity** | Informational |
| **Locations** | `lean/Kopis/Properties/GenMatrix.lean:57-117` (and AVX2/NEON twins); `lean/Kopis/Neon/Model.lean:228-262`; `lean/SpecTests/Avx2/Run.lean:241-260`; `build.rs:130-140` |

**Description.**
1. **The hash axioms are over-general.** They state that the `turboshake` crate computes `Spec.TurboSHAKE` for *every* `RATE` and `DS`, whereas the crate rejects invalid values at compile time. The axioms are consistent (a list-based model exists) and harmless for the instances used. They are nonetheless the single most important trusted correspondence: every KEM-level hash in every backend (KGEXPAND, PKHASH, FO, NOREJECT) and serial GenMat/GenSecret go through them.
2. **The memory axioms are not linked to the models the silicon vectors test.** For the 12 AVX2 and 7 NEON load/store axioms, no theorem ties the axiom to the model that the silicon vectors exercise; the models are written ad hoc in the test runners. A divergence between axiom text and model would go unnoticed. The non-memory axioms *are* tied to their models, by `Model.lean`.
3. **Little-endianness is implicit.** The NEON memory axioms bake in a little-endian layout, and `build.rs` does not exclude `aarch64_be`.
4. **Documentation drift.**
   * `lean/Makefile:183` names `ref_test_vectors-*.jsonl`.
   * `Makefile:191` and `SpecTests/Avx2/Run.lean:7` give "42 axioms"; there are 50.
   * `Makefile:142, 162` reference missing plan documents.
   * `extract_rust_to_lean.sh:58` labels the NEON step "AVX2".
   * `TrustBase.lean:55` contains the typo "sutble".

**Recommendation.**
* Restrict the hash axioms to the instantiated `(RATE, DS)` pairs.
* Prove the memory-axiom/model equivalence.
* Reject `target_endian = "big"` in `neon_is_available`.

---

### OPUS55-KOPIS-016: Secret-key accessor is undocumented

| | |
|---|---|
| **Severity** | Informational (prior L6, partially fixed) |
| **Locations** | `src/kem.rs:107-109` |

**Description.** `KemSecretKey::as_bytes()` returns the 32-byte seed, which is the complete long-term secret, and the function has no documentation at all. Bytes copied out of it escape `ZeroizeOnDrop`. The other half of prior L6 has been addressed: `SharedSecret` now implements `ConstantTimeEq` (`src/kem.rs:58-62`).

**Recommendation.** Document that this value *is* the secret key and must be handled and erased accordingly.

---

### OPUS55-KOPIS-017: Dependency and metadata hygiene

| | |
|---|---|
| **Severity** | Informational |
| **Locations** | `Cargo.toml:4, 12`; `build.rs:48, 97`; `.github/workflows/ci.yml:6, 9` |

**Description.**
* **`turboshake` is pinned only by semver range.** It is pinned as `"0.7"`, a single-maintainer crate on whose correctness every KEM hash depends (prior M5). Review of 0.7.1 found:
  * `#![forbid(unsafe_code)]`;
  * DS validated at compile time to 0x01..=0x7F;
  * correct padding;
  * length-only branching.

  The residual risk is a future 0.7.x release being picked up automatically.
* **Dead cfg.** `kopis_neon_assume` is emitted but never read.
* **Deprecated licence syntax.** `license = "MIT/Apache-2.0"` uses deprecated SPDX syntax.
* **README changes skip CI.** `paths-ignore: ["README.md"]` skips CI even though the README is compiled as a doctest (`src/lib.rs:12`).

**Recommendation.**
* Pin `turboshake = "=0.7.1"`, or vendor and review it.
* Remove the dead cfg.
* Use `"MIT OR Apache-2.0"`.
* Drop the `paths-ignore`.

---

### OPUS55-KOPIS-018: No data-independent-timing mode on AArch64

| | |
|---|---|
| **Severity** | Informational |

**Description.** Apple and Arm document PSTATE.DIT as the mechanism that guarantees data-independent latency for the instructions in its list on recent cores, Apple M-series included. Kopis does not set it, so constant-time behaviour on AArch64 rests on the observed (rather than architecturally guaranteed) timing of `mul`, `sqdmulh` and similar instructions.

**Recommendation.** Document this. Optionally, offer a feature that sets DIT for the duration of each public call, where the operating system permits it.

---

## 5. Areas Reviewed Without Findings

**Specification conformance (Rust vs `lean/kopis-spec.md`).** Checked by hand against the spec and against `lean/Spec/Kopis/Spec.lean`:
* **Key generation** (`src/pke.rs:134-183`):
  * `TurboSHAKE256(sk ‖ ℓ, 96, 0x01)` is split as A-seed ‖ s-seed ‖ z;
  * b = (Aᵀs + 4) >> 3;
  * pk = pack10(b) ‖ seed;
  * pkh = `TurboSHAKE256(pk, 32, 0x04)`.

  The non-10-bit residue left in the cached `b` (bits 10–12) contributes only multiples of 2^10 to v′ and is masked by T-bit serialization. Keygen-cached and `from_bytes` public keys therefore encrypt bit-identically, which the FO re-encryption comparison requires; the KATs confirm this.
* **Encryption:**
  * b′ = (A·s′ + 4) >> 3, with A·s′ (not Aᵀ·s′);
  * c_m = (bᵀs′ − m·2^9 + 4) >> (10 − t).
* **Decryption:** m′ = ((v − c_m·2^(10−t) + h2) >> 9) & 1, with h2 = 256 − 2^(9−t) + 4.
* **KEM:**
  * k ‖ r = `TurboSHAKE256(m ‖ pkh, 64, 0x05)`;
  * the rejection value is `TurboSHAKE256(z ‖ c, 32, 0x06)`;
  * the comparison uses `subtle` slice `ct_eq` and the selection uses `conditional_select` (`src/kem.rs:179-183`).

  Both candidate keys are always computed.
* **GenMat:** `TurboSHAKE128(seed ‖ i ‖ j, 416, 0x02)`, unpacked as 13-bit fields, with no rejection.
* **GenSecret:** `TurboSHAKE256(seed ‖ i, 32μ, 0x03)`. CBD takes LSB-first μ/2-bit groups. The specialised μ = 6/8/10 paths match a naive bit-by-bit reference (`src/sample.rs` tests). The AVX2 and NEON paths match serial on random inputs and on the XOF definition.
* **Sizes and domain separators:** all six domain separators lie in [0x01, 0x7F] and are pairwise distinct; the sizes 672/736, 992/1088 and 1312/1472 all match.

**Input validation.**
* Every 10-bit packing is canonical, and every byte string of length 32·(10ℓ) + 32 is a valid public key.
* `from_bytes` stores the bytes verbatim, so pkh = H(input bytes), with no malleability.
* Ciphertexts are fixed-size arrays at the API boundary, and the `assert_eq!` on length at `src/kem.rs:150` is proved unreachable by Lean.
* Attacker-controlled b and b′ are < 2^10, well inside the `from_uniform` precondition of [0, 2^13).

**Arithmetic, verified exhaustively or by certified interval propagation (`numcheck/`, plus the NEON model in `neon/bounds/`).**
* Barrett reduction is congruent, with max |r| = q/2 exactly over all 2^16 inputs for both primes.
* `mont_mul` is congruent for all 2^16 inputs × 512 twiddles (±), and |r| ≤ |az|/2^16 + q/2 exactly.
* NEON's `sqdmulh`/`shsub` formulation never saturates (no constant equals −2^15).
* The i32 accumulator stays within 1.16·10^8 < 2^31.
* Garner's t is canonical, and a₁ + q₁t < 2^31.
* All constants were checked: q⁻¹, the Barrett multipliers, `INVNTT_SCALE`, `CRT_Q1_INV_MONT`, and both 512th roots and tables. Worst-case extremal products are exercised by `extremal_coefficients`.

**Constant time (control flow and addressing).** No secret-dependent branch, secret-indexed load or division exists in any backend. Specifically:
* CBD uses `count_ones` (SWAR/`popcnt`), `vpshufb` with a register-resident table, or NEON `cnt`;
* serialization loops are bounded by public counters;
* the CRT centering uses masks (`src/arithmetic/ntt_crt.rs:897-908`);
* backend dispatch branches only on CPU features.

Valgrind taint checking (12 checks: three parameter sets × keygen/encap/import-encap/decap, with valid, bit-flipped and garbage ciphertexts, and with the *whole* `KemSecretKey` and the ciphertext tainted) reports 0 errors for serial, forced AVX2, and the default baseline runtime-dispatch build.

The AArch64 disassembly (`harness2`) shows that every conditional branch in `ntt_block`, `reduce_invntt`, `permute`, `xof2`, `gen_*`, `decrypt`, `expand_secret_key` and `decapsulate` compares a loop counter or a constant flag. `tbl` appears only with constant control vectors.

**SIMD Keccak.**
* AVX2 `xof4` and NEON `xof2` use the correct round constants `RC[12..24]`, ρ offsets and π rows, and correct padding (DS at the first free byte, 0x80 ORed into the last rate byte, including the case where both land on the same byte).
* Multi-block squeeze was checked against `turboshake` over rates 168/136, DS 0x01/02/03/1F/7F, and output lengths 1–1000 (520 NEON lanes; the AVX2 `matches_scalar` test).
* For odd ℓ, the lane batching duplicates the last index and discards it; the indices are correct.

**Memory safety (apart from OPUS55-KOPIS-002).**
* All pointer casts are to unaligned loads/stores.
* The AVX2 `ser::deserialize` tail copy (≤ 15 bytes into 32) and the shuffle windows (≤ byte 14) are in bounds.
* The prior Informational finding about aligned loads on a `repr(Rust)` `Plan` is resolved; `load_u8` and `load_i32` are unaligned.
* `deny(unsafe_code)` holds outside the backends, and the crate is `forbid(unsafe_code)` in serial builds (`src/lib.rs:4-5`).
* The CPUID probe checks OSXSAVE and XCR0 bits 1 and 2 via `cpufeatures` before trusting the AVX2 bit.

**API.**
* `SharedSecret` and `KemSecretKey` are `ZeroizeOnDrop` and not `Debug`.
* `SharedSecret` is not `Clone` and has constant-time equality.
* No public entry point can panic for well-typed input, which Lean proves for the extracted paths.

**Dependencies.** The normal dependency graph is exactly `cpufeatures`, `rand_core`, `subtle`, `turboshake` (→ `digest`, `keccak`, `sponge-cursor`) and `zeroize`, all from the registry. The `[patch]` and git entries are dev-only, as confirmed by `cargo tree -e normal -i aws-lc-rs`. The `subtle 2.6.1` slice `ct_eq` returns early only on length mismatch, and the lengths are public here.

---

## 6. Status of Findings from the 2026-07-30 Report

| Prior ID | Title (abridged) | Status at `2aec76b` |
|---|---|---|
| H1 | NEON enabled on softfloat AArch64 | **Fixed.** `build.rs:130-140` requires `neon`, `sha3` and a non-softfloat ABI. Raw-cfg bypass remains (OPUS55-KOPIS-003). |
| H2 | KAT provenance unverifiable / duplicated pqm4 files | **Changed.** pqm4 files removed; provenance still unrecorded (OPUS55-KOPIS-014). |
| H3 | CI never exercises NEON | **Fixed.** `macos-latest` runs forced-NEON and autodetect tests, plus a cross `no_std` build. No Linux/aarch64 job and no dynamic CT check for NEON (OPUS55-KOPIS-005). |
| M1 | Forced AVX2 accepts host CPU | **Still present** (OPUS55-KOPIS-003; re-rated Low). |
| M2 | AVX2 Barrett schedule mis-documented | **Fixed.** Module docs state the 3,4,1 schedule and the table-dependent bound. Independently re-verified: worst lane 30,674. |
| M3 | Intermediate secrets not zeroized | **Still present**, now demonstrated (OPUS55-KOPIS-001; re-rated Low). |
| M4 | CI does not verify Lean | **Fixed.** CI checks extraction currency, builds all three proof stacks, enforces the axiom gate, and runs the spec and intrinsic-model tests. |
| M5 | `turboshake` semver pin | **Still present** (OPUS55-KOPIS-017). |
| L1 | Safe `#[target_feature]` fns with length preconditions | **Mostly fixed.** Accessors now bounds-check internally, but the checks wrap (OPUS55-KOPIS-002). |
| L2 | AVX2 CBD admits μ = 12 | **Still present** (OPUS55-KOPIS-010). |
| L3 | Wrong arithmetic comments (serial) | **Changed.** The `pke.rs` comment is now correct; new stale comments exist in `ntt_arith.rs` (OPUS55-KOPIS-011). |
| L4 | `debug_assert!` arithmetic bounds | **Partially fixed** (OPUS55-KOPIS-012). |
| L5 | KAT test can pass vacuously | **Still present** (OPUS55-KOPIS-014). |
| L6 | Seed accessor lacks warning; no CT equality on `SharedSecret` | **Partially fixed.** `ConstantTimeEq` was added; the accessor is now undocumented (OPUS55-KOPIS-016). |
| L7 | Backend tests skip silently | **Still present.** Every backend test begins `if !available() { return; }`. Mitigated by forced-backend CI legs. |
| L8 | README pushes skip CI | **Still present** (OPUS55-KOPIS-017). |
| L9 | Secret types derive `Debug`/`PartialEq`/`Copy` | **Still present** (OPUS55-KOPIS-013). |
| Info | `kopis_neon_assume` dead; licence string; `cargo hack` vacuous; aligned loads on `Plan` | Dead cfg and licence string still present. `cargo hack` removed. Aligned-load issue fixed. |

---

## 7. The Formal-Verification Assurance Argument

### 7.1 What is proved

`lean/TopLevelTheoremsSerial.lean` states six theorems. They are quantified over `Size ∈ {k512, k768, k1024}` and have **no hypotheses beyond typing**, so none can be vacuous. `TopLevelTheoremsAvx2.lean` and `TopLevelTheoremsNeon.lean` are generated from it by `sed` (`lean/Makefile:57-77`). After normalisation their statements are identical, and each is proved against its own extraction.

The notation `x ⦃ p ⦄` means `∃ v, x = ok v ∧ p v`, so every theorem is a total-correctness statement that excludes Aeneas `fail` (panic, including arithmetic overflow under checked semantics) and divergence.

| Theorem | Statement (paraphrased) |
|---|---|
| `keygen_then_to_bytes` | `pk.to_bytes()` after `expand_from_seed(seed)` equals `SkToPk(seed)` |
| `keygen_then_encapsulate` | `encapsulate_deterministic(r)` on that pk equals `KemEncap(r, SkToPk(seed))` |
| `from_bytes_then_encapsulate` | for **every** pk byte string, `from_bytes` then encapsulate equals `KemEncap(r, pk_bytes)` |
| `pk_from_bytes_then_to_bytes` | byte round-trip (not tied to the spec) |
| `sk_from_bytes_then_to_bytes` | seed round-trip (not tied to the spec) |
| `keygen_then_decapsulate` | for **every** ciphertext array, `decapsulate` equals `KemDecap(seed, ct)`, including the exact implicit-rejection value |

Under its assumptions, this establishes functional equivalence to the specification for all inputs in all three backends. It also proves that the bounds `assert!`s in the intrinsic accessors, and the length assertion in `decap`, never fire on these paths.

The Lean spec (`lean/Spec/Kopis/Spec.lean`) was compared line by line with `lean/kopis-spec.md`; **no semantic discrepancy was found**. The TurboSHAKE spec follows RFC 9861.

### 7.2 What is assumed

The gate `lean/TrustBase.lean:321-345` collects the axioms of every constant under `Kopis.TopLevel{Serial,Avx2,Neon}`. It fails if any axiom is missing from the audited list, and also if any listed axiom is unused. It runs in CI, which makes it equivalent to an enforced `#print axioms` check. There are no occurrences of `sorry`, `native_decide`, `implemented_by`, `@[extern]` or `partial def`. The trusted items are:

* **Lean core:** `propext`, `Classical.choice`, `Quot.sound`.
* **`turboshake` (5 axioms per backend).** These cover `default`, `update`, `finalize_xof`, and `read` at rates 168 and 136, asserting that the crate computes the Lean TurboSHAKE spec. In the serial backend every hash goes through them. In AVX2 and NEON, GenMat and GenSecret use the in-crate `xof4`/`xof2`, which **are proved** against the spec; KGEXPAND, PKHASH, FO and NOREJECT still use the axioms. See OPUS55-KOPIS-015 on their over-generality.
* **`subtle` (2 axioms).** Slice `ct_eq` is true iff the values are equal; `conditional_select` behaves as described. Both are functional only and say nothing about timing.
* **`count_ones`** for u8 and u16. On NEON, also `wrapping_neg` and `div_ceil`. All are correct as stated.
* **Intrinsics:** 50 AVX2 and 46 NEON instruction axioms. Every axiom was checked against the Intel SDM and the Arm ARM, and no incorrect statement was found. Examples:
  * signed `vpmulhw`;
  * per-128-bit-lane `vpackssdw`/`vpackusdw` with saturation;
  * `vpshufb` zeroing on bit 7;
  * shift counts past the lane width;
  * `vperm2i128` zeroing on bit 3;
  * saturating `sqdmulh`, including the −2^15·−2^15 case;
  * `ushl` using the signed low byte;
  * `bcax`/`rax1`/`xar` operand order.

  Non-memory axioms are proved to determine computable models, and those models are replayed against 54,279 (AVX2) and 50,176 (NEON, Apple M1) vectors recorded from silicon, in CI. The NEON file was regenerated independently under qemu and is byte-identical. The memory axioms lack this link (OPUS55-KOPIS-015).
* **AVX2 only:** four `bv_decide` native axioms (OPUS55-KOPIS-006), and the redundant `available_ok` (OPUS55-KOPIS-004).
* **Toolchain:** Charon, Aeneas (including its Lean models of core integer, slice and array operations), rustc, LLVM and the Lean kernel. The Aeneas and Charon binaries are downloaded without checksum verification (`extract_rust_to_lean.sh:24-31`). CI does verify that the committed extraction matches a fresh one.

### 7.3 Gaps between "proved" and "secure"

1. **Side channels.** Nothing in the proofs constrains timing, branches or memory access. The constant-time claims rest on ct-check (OPUS55-KOPIS-004, OPUS55-KOPIS-005) and on manual review.
2. **Secret erasure.** Aeneas does not model `Drop`, and the `zeroize` calls are opaque. OPUS55-KOPIS-001 is outside the proof's reach.
3. **Cryptographic security.** There is no theorem about IND-CCA security, decryption-failure probability, or even Decap∘Encap = k. The spec is proved to be *implemented*, not proved to be *secure*. Its security rests on the Saber and FO literature.
4. **Code that is not covered:**
   * `generate_from_rng` and `encapsulate_with_rng`. They are thin wrappers, extracted but not mentioned in any theorem.
   * The runtime CPUID dispatch of the default x86 build (OPUS55-KOPIS-004).
   * Everything behind the `turboshake` axioms in serial mode.
5. **Compilation.** The proofs concern the MIR that Charon sees, under checked-arithmetic semantics. Release builds wrap instead; this is equivalent on the proved paths because overflow is proved absent. Codegen-introduced behaviour, such as LLVM converting masks into branches, is out of scope by construction. It is precisely what ct-check exists to catch.

Within those boundaries, the formal-verification effort is substantive and well engineered: total correctness for all inputs, an enforced axiom whitelist, intrinsic axioms validated against silicon, and extraction currency checked in CI. The residual risk sits in the trusted hash correspondence and in the properties the proofs do not attempt to cover, rather than in the proofs themselves.
