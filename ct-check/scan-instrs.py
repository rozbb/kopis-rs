#!/usr/bin/env python3
"""Scans kopis's compiled code for instructions whose latency depends on their operands.

This is the half of constant-time checking that Valgrind cannot do. Memcheck reports branches and
memory addresses that depend on a secret, which is most leaks, but it is blind to a `div` whose
divisor is secret: the taint flows through the quotient without ever reaching a branch. Nothing in
the definedness model notices that the instruction took a different number of cycles.

So this pass works the other way round, on the instruction stream instead of the data. It cannot
tell a secret operand from a public one — that is what the allowlist is for — but it sees every
target we can cross-compile to, including the NEON backend that Valgrind cannot run here.

Two failure modes are worth knowing about, because both fail *toward* a clean report:

  * the host `objdump` is usually built for one architecture and prints nothing at all for the
    others, exiting 0 while doing so. We use `llvm-objdump` and assert we actually saw code.
  * the API is const-generic, so `libkopis.rlib` on its own need not hold every instantiation.
    That is what `ct-check/probe` is for; we disassemble it alongside kopis and every dependency
    that ends up in the target binary.

Calls to compiler-rt division helpers (`__udivti3`, `__aeabi_uldivmod`, ...) are flagged too: a
divide too wide for the hardware becomes one of these instead of a `div`. They are found through
the call's relocation, since the callee is not in the rlib.

x86 and AArch64 are checked against an allowlist rather than a denylist: the vendor's published
data-independent-timing instructions (Intel's DOIT list in `x86-doit.txt`, Arm's DIT list in
`aarch64-dit.txt`) plus the few in `X86_EXTRA` / `AARCH64_EXTRA`. Anything else is reported.
32-bit Arm still uses a denylist, since M-profile cores have no DIT list.
"""

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
ALLOWLIST = Path(__file__).resolve().parent / "instr-allowlist.txt"
X86_DOIT = Path(__file__).resolve().parent / "x86-doit.txt"
AARCH64_DIT = Path(__file__).resolve().parent / "aarch64-dit.txt"

# If a disassembly yields fewer instructions than this, something went wrong with the tooling
# rather than the code being small; treat it as an error instead of a pass.
MIN_PLAUSIBLE_INSNS = 2000

# Instruction classes whose timing can depend on operand *values*, for 32-bit Arm. Deliberately
# absent, because they are constant-time on every CPU this crate targets and would only add noise:
# variable-count shifts, CLZ, integer MUL, and conditional execution.
DIV_LIBCALL = (
    "div-libcall",
    r"^R_\S+ (__u?(div|mod|divmod)[sdt]i[34]|__aeabi_u?l?div(mod)?|__aeabi_u?idiv(mod)?)\b",
    "Call to a software divide: as variable-time as the instruction it replaces",
    None,
)

CATEGORIES = {
    # Only the relocation check: x86 and AArch64 instructions go through their allowlists.
    "x86": [DIV_LIBCALL],
    "aarch64": [DIV_LIBCALL],
    # A32/T32. Long multiply is deliberately absent: `UMULL` and friends early-terminate on
    # Cortex-M3 and below, but the crate does not claim constant time on those cores, and on the
    # Cortex-M4/M7 that `thumbv7em` targets the multiply is single-cycle.
    "arm": [
        ("int-div", r"^[us]div[a-z]*\b",
         "UDIV/SDIV: early-terminating on Cortex-M (suffix allows IT-block forms like `udivne`)",
         None),
        ("fp-div-sqrt", r"^(vdiv|vsqrt)[a-z]*", "FP divide/sqrt: variable latency", None),
        DIV_LIBCALL,
    ],
}


def arch_family(target: str) -> str:
    if target.startswith(("x86_64", "i686", "i586")):
        return "x86"
    if target.startswith("aarch64"):
        return "aarch64"
    if target.startswith(("thumb", "arm")):
        return "arm"
    return ""


# x86 instructions that are not on Intel's list but are accepted anyway. Each is a claim that the
# instruction's timing does not depend on its data. The scan fails if an entry stops being needed.
#
# Where kopis's own code produced a non-DOIT instruction, it has been changed not to: the AVX2
# intrinsics that LLVM would rewrite are pinned with inline assembly, and `cbd_diff` is always
# inlined so it never needs BZHI. What is left is chosen by LLVM regardless of the source.
X86_EXTRA = {
    # Control flow. A secret-dependent branch is phase 1's to find.
    "call": "control flow",
    "ret": "control flow",
    "nop": "no operands",
    "ud2": "no operands",
    # LLVM's default encodings for copying and zeroing vectors: every register-to-register copy,
    # every `memcpy`/`memset` it inlines (including in dependencies), and the zeroing idiom. No
    # source change reaches these, and the legacy forms MOVAPS, MOVUPS, and XORPS are listed.
    "vmovaps": "VEX form of MOVAPS, which is listed",
    "vmovups": "VEX form of MOVUPS, which is listed",
    "vxorps": "VEX form of XORPS, which is listed",
    # The serial backend's vectorized loops on baseline x86-64. SSE2 has no integer instruction
    # that blends the 64-bit halves of two registers, so LLVM uses these.
    "movsd(sse)": "legacy-SSE form of VMOVSD, which is listed",
    "movupd": "MOVUPS with a 66 prefix; the same move",
    "shufps": "fixed lane shuffle; PSHUFD, the one-source integer equivalent, is listed",
}
X86_BRANCH = re.compile(r"^j[a-z]+$")

# Non-DOIT x86 instructions that get a readable category. Anything else not on the list reports as
# `non-doit:<mnemonic>`, so an allowlist entry has to name the mnemonic it excuses.
X86_NAMED = [
    ("int-div", r"^i?div$", "DIV/IDIV: latency depends on the operands"),
    ("pext-pdep", r"^(pext|pdep)$", "BMI2: microcoded and mask-dependent on AMD Zen 1/2"),
    ("fp-div-sqrt", r"^v?(div|sqrt)[ps][sd]$",
     "FP divide/sqrt: variable latency, plus subnormal penalties"),
    ("rep-string-cmp", r"^rep[a-z]*_(cmps|scas)",
     "REP CMPS/SCAS: terminates early depending on the data"),
    ("gather", r"^v?p?gather", "Gather: timing follows the address pattern"),
]

X86_IGNORED_PREFIXES = {"data16", "cs", "ds", "es", "fs", "gs", "ss", "notrack", "lock"}
X86_REP_PREFIXES = {"rep", "repe", "repz", "repne", "repnz"}
# LLVM's condition-code spellings, mapped to the ones Intel's list uses.
X86_CC = {"e": "z", "ne": "nz", "ae": "nb", "nae": "b", "c": "b", "nc": "nb", "a": "nbe",
          "na": "be", "ge": "nl", "nge": "l", "g": "nle", "ng": "le", "pe": "p", "po": "np"}


def x86_mnemonic(text: str) -> str:
    """The mnemonic of an Intel-syntax instruction, spelled as Intel's DOIT list spells it."""
    words = text.split()
    while words and words[0] in X86_IGNORED_PREFIXES:
        words = words[1:]
    if not words:
        return ""
    m = words[0]
    if m in X86_REP_PREFIXES and len(words) > 1:
        return f"{m}_{words[1]}"
    if m == "movabs":
        return "mov"
    # MOVSD is both a string move (listed) and an SSE scalar move (not).
    if m == "movsd" and "xmm" in text:
        return "movsd(sse)"
    cc = re.match(r"^(cmov|set)([a-z]+)$", m)
    if cc and cc.group(2) in X86_CC:
        return cc.group(1) + X86_CC[cc.group(2)]
    return m


# AArch64 instructions that are not on Arm's list but are accepted anyway, as for X86_EXTRA. The
# one in kopis's own code, an `fneg` LLVM used to build the Keccak padding word, was removed by
# pinning `set_u64x2` with inline assembly; these come from LLVM regardless of the source.
AARCH64_EXTRA = {
    # Immediates with no data operand: constants and PC-relative addresses.
    "adrp": "PC-relative address; no data operand",
    "movz": "MOVZ/MOVN, or ORR (immediate), which is listed; no data operand",
    "movk": "inserts an immediate field; the timing cannot depend on the other bits",
    "movi": "Advanced SIMD modified immediate, like the listed BIC/ORR; no data operand",
    "mvni": "Advanced SIMD modified immediate, like the listed BIC/ORR; no data operand",
    # Moves between a general and a SIMD&FP register, which LLVM picks for 64-bit lanes. The
    # same transfer as the listed INS and UMOV. Other FMOV forms are not covered.
    "fmov(general)": "GPR to SIMD&FP register transfer, like the listed INS/UMOV",
}
AARCH64_BRANCH = re.compile(r"^(b|bl|br|blr|ret|cbn?z|tbn?z)(\.[a-z]+)?$")

# Non-DIT AArch64 instructions that get a readable category, as for X86_NAMED.
AARCH64_NAMED = [
    ("int-div", r"^[us]div$", "UDIV/SDIV: early-terminating on Cortex-A and Neoverse"),
    ("fp-div-sqrt", r"^(fdiv|fsqrt)$", "FP divide/sqrt: variable latency"),
]

# Aliases that llvm-objdump prints even under `-M no-aliases`, mapped to the instruction Arm lists.
# Shifts by an immediate are bitfield moves; shifts by a register are the `*V` forms.
AARCH64_ALIASES = {
    "lsl": ("ubfm", "lslv"), "lsr": ("ubfm", "lsrv"), "asr": ("sbfm", "asrv"),
    "ror": ("extr", "rorv"),
    "bfi": ("bfm", None), "bfxil": ("bfm", None), "bfc": ("bfm", None),
    "ubfiz": ("ubfm", None), "ubfx": ("ubfm", None), "uxtb": ("ubfm", None),
    "uxth": ("ubfm", None),
    "sbfiz": ("sbfm", None), "sbfx": ("sbfm", None), "sxtb": ("sbfm", None),
    "sxth": ("sbfm", None), "sxtw": ("sbfm", None),
}
AARCH64_GPR = re.compile(r"^([wx]([0-9]+|zr)|w?sp)$")


def aarch64_mnemonic(text: str) -> str:
    """The mnemonic of a `-M no-aliases` A64 instruction, spelled as Arm's DIT list spells it."""
    m, _, rest = text.partition(" ")
    ops = [o.strip() for o in rest.split("//")[0].split(",")]
    if m in AARCH64_ALIASES:
        imm, reg = AARCH64_ALIASES[m]
        return imm if reg is None or ops[-1].startswith("#") else reg
    if m == "mov":
        # The forms LLVM still prints as MOV: an immediate, or a vector element.
        if ops[-1].startswith("#"):
            return "movz"
        if "[" in ops[0]:
            return "ins"
        if "[" in ops[-1]:
            return "umov" if AARCH64_GPR.match(ops[0]) else "dup"
        return "orr"
    if m == "fmov" and len(ops) == 2 and sum(bool(AARCH64_GPR.match(o)) for o in ops) == 1:
        return "fmov(general)"
    return m


# Per family: the vendor list, the extra exceptions, the mnemonic normalizer, the branch pattern,
# and the readable categories for what is not on the list.
ALLOWLISTED = {
    "x86": (X86_DOIT, X86_EXTRA, x86_mnemonic, X86_BRANCH, X86_NAMED, "non-doit",
            "not on Intel's DOIT list (ct-check/x86-doit.txt)"),
    "aarch64": (AARCH64_DIT, AARCH64_EXTRA, aarch64_mnemonic, AARCH64_BRANCH, AARCH64_NAMED,
                "non-dit", "not on Arm's DIT list (ct-check/aarch64-dit.txt)"),
}
EXTRA_USED = {fam: set() for fam in ALLOWLISTED}


def load_doit(path: Path) -> set:
    return {line.strip().lower() for line in path.read_text().splitlines()
            if line.strip() and not line.startswith("#")}


def classifier(fam: str, target: str):
    """A function from one disassembled row to the [(category, description)] it falls under."""
    cats = [
        (name, re.compile(pattern), desc)
        for name, pattern, desc, only_on in CATEGORIES[fam]
        if only_on is None or re.match(only_on, target)
    ]

    def by_regex(text):
        return [(name, desc) for name, rx, desc in cats if rx.match(text)]

    if fam not in ALLOWLISTED:
        return by_regex

    path, extra, mnemonic, branch, named, prefix, why = ALLOWLISTED[fam]
    listed = load_doit(path)
    named = [(name, re.compile(pattern), desc) for name, pattern, desc in named]

    def classify_allowlisted(text):
        if text.startswith("R_"):
            return by_regex(text)
        m = mnemonic(text)
        if m in extra:
            EXTRA_USED[fam].add(m)
            return []
        if m in listed or branch.match(m):
            return []
        for name, rx, desc in named:
            if rx.match(m):
                return [(name, desc)]
        return [(f"{prefix}:{m}", why)]

    return classify_allowlisted


def host_target() -> str:
    out = subprocess.run(["rustc", "-vV"], capture_output=True, text=True, check=True).stdout
    for line in out.splitlines():
        if line.startswith("host: "):
            return line[6:].strip()
    raise SystemExit("scan-instrs: could not determine the host target from `rustc -vV`")


def installed_targets() -> set:
    out = subprocess.run(["rustup", "target", "list", "--installed"],
                         capture_output=True, text=True)
    return set(out.stdout.split()) if out.returncode == 0 else set()


def find_llvm_objdump() -> str:
    found = shutil.which("llvm-objdump")
    if found:
        return found
    # Shipped by the `llvm-tools` rustup component. Prefer the active toolchain's copy, but any
    # toolchain's will do — it is only being used as a disassembler.
    sysroot = subprocess.run(["rustc", "--print", "sysroot"],
                             capture_output=True, text=True, check=True).stdout.strip()
    for cand in Path(sysroot).glob("lib/rustlib/*/bin/llvm-objdump"):
        return str(cand)
    import os
    rustup_home = Path(os.environ.get("RUSTUP_HOME", Path.home() / ".rustup"))
    for cand in sorted(rustup_home.glob("toolchains/*/lib/rustlib/*/bin/llvm-objdump")):
        return str(cand)
    raise SystemExit(
        "scan-instrs: llvm-objdump not found.\n"
        "  Install it with `rustup component add llvm-tools`, or put llvm-objdump on PATH.\n"
        "  The system `objdump` is not a substitute: it is typically built for one architecture\n"
        "  and prints nothing, successfully, for every other one."
    )


def all_configs(host: str):
    """Every (label, target, backend, rustflags) worth scanning from this host."""
    out = []
    fam = arch_family(host)
    if fam == "x86":
        out.append(("host/serial", host, 'serial', '--cfg kopis_backend="serial"'))
        out.append(("host/avx2", host, "avx2",
                    '-C target-feature=+avx2 --cfg kopis_backend="avx2"'))
        # A modern CPU and a size-optimized build. The configs above have no POPCNT/LZCNT/TZCNT,
        # and at opt-level 3 LLVM vectorizes the loops that would use them, so a `count_ones` on
        # secret data passes both. This is the build where it shows up.
        out.append(("host/v3-size", host, "native", "-C target-cpu=x86-64-v3 -C opt-level=s"))
    elif fam == "aarch64":
        out.append(("host/serial", host, "serial", '--cfg kopis_backend="serial"'))
        out.append(("host/neon", host, "neon",
                    '-C target-feature=+neon,+sha3 --cfg kopis_backend="neon"'))

    # Cross targets. These need no linker: an rlib is just an archive, so `cargo build` for a
    # bare-metal target works without a cross toolchain installed.
    cross = [
        ("aarch64-none/serial", "aarch64-unknown-none", "serial", '--cfg kopis_backend="serial"'),
        ("aarch64-none/neon", "aarch64-unknown-none", "neon",
         '-C target-feature=+neon,+sha3 --cfg kopis_backend="neon"'),
        ("thumbv7em/serial", "thumbv7em-none-eabi", "serial", '--cfg kopis_backend="serial"'),
    ]
    return out + [c for c in cross if c[1] != host]


def configs(host: str, installed: set):
    """The subset of `all_configs` whose target is installed."""
    out = []
    for label, target, backend, flags in all_configs(host):
        if target == host or target in installed:
            out.append((label, target, backend, flags))
        else:
            print(f"  skipping {label}: target {target} not installed "
                  f"(`rustup target add {target}`)")
    return out


def build(target: str, rustflags: str) -> list:
    """Builds the probe for one configuration; returns its rlib and those of every dependency
    compiled for `target` (build-time dependencies such as proc macros are built for the host and
    never reach the binary)."""
    # The allowlist matches on symbol names, so the mangling is pinned rather than left to the
    # toolchain's default: rustc 1.98 emits v0, 1.96 emitted the legacy scheme, and an entry
    # written for one spelling stops covering its divide under the other, failing the scan on a
    # divide that was fine yesterday and is still fine today. Pinning also
    # keeps llvm-objdump from having to fall back to the `$LT$..$GT$` form it prints when it
    # declines to demangle a legacy symbol.
    env = {**__import__("os").environ,
           "RUSTFLAGS": f"{rustflags} -C symbol-mangling-version=v0"}
    proc = subprocess.run(
        ["cargo", "build", "-p", "ct-scan-probe", "--release", "--target", target,
         "--message-format=json-render-diagnostics"],
        cwd=REPO, env=env, capture_output=True, text=True,
    )
    if proc.returncode != 0:
        print(proc.stderr, file=sys.stderr)
        raise SystemExit(f"scan-instrs: build failed for {target} ({rustflags})")

    rlibs = []
    for line in proc.stdout.splitlines():
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if msg.get("reason") != "compiler-artifact":
            continue
        rlibs += [f for f in msg.get("filenames", [])
                  if f.endswith(".rlib") and f"/{target}/" in f]
    return rlibs


def disassemble(objdump: str, rlibs: list, fam: str):
    """Yields (symbol, instruction-text) and the total instruction count. Relocations are yielded
    as rows too, as `R_<type> <target>`, but not counted. x86 is in Intel syntax, whose mnemonics
    carry no operand-size suffix and so match Intel's DOIT list directly. AArch64 is printed
    without aliases (`madd`, not `mul`), which is how Arm's DIT list names instructions."""
    syntax = {"x86": ["-M", "intel"], "aarch64": ["-M", "no-aliases"]}.get(fam, [])
    proc = subprocess.run([objdump, "-d", "-r", "--demangle", "--no-show-raw-insn", *syntax,
                           *rlibs], capture_output=True, text=True)
    sym, total, rows = None, 0, []
    for line in proc.stdout.splitlines():
        header = re.match(r"^[0-9a-f]+ <(.+)>:", line)
        if header:
            sym = header.group(1)
            continue
        insn = re.match(r"^\s*[0-9a-f]+:\s+(\S.*)$", line)
        if not insn or sym is None:
            continue
        text = " ".join(insn.group(1).split())
        if not text.startswith("R_"):
            total += 1
        rows.append((sym, text))
    return rows, total


def load_allowlist(path: Path):
    entries = []
    if not path.is_file():
        return entries
    for raw in path.read_text().splitlines():
        line = raw.split("#", 1)[0].strip() if not raw.lstrip().startswith("#") else ""
        if not line:
            continue
        parts = [p.strip() for p in line.split("|")]
        if len(parts) < 3:
            raise SystemExit(f"scan-instrs: malformed allowlist line: {raw!r}")
        entries.append((parts[0], parts[1], parts[2]))
    return entries


# --------------------------------------------------------------------------------------------
# Self-test
#
# The scan's failure mode is silence: a regex that stopped matching, a disassembler whose output
# format moved, or an allowlist entry broad enough to swallow a real finding all produce a clean
# report rather than an error. None of that is visible from a passing run, so the checks below
# plant things the scanner is required to find. `ct-check.sh --selftest` runs them alongside the
# Valgrind negative control.
# --------------------------------------------------------------------------------------------

# (arch family, instruction text, category it must be reported as, or None for "must stay silent")
MATCHER_CASES = [
    ("x86", "div ecx", "int-div"),
    ("x86", "idiv rbx", "int-div"),
    ("x86", "div r14b", "int-div"),
    ("x86", "pext rcx, rbx, rax", "pext-pdep"),
    ("x86", "pdep eax, ecx, edx", "pext-pdep"),
    ("x86", "divss xmm0, xmm1", "fp-div-sqrt"),
    ("x86", "vsqrtpd ymm0, ymm1", "fp-div-sqrt"),
    ("x86", "sqrtsd xmm0, xmm1", "fp-div-sqrt"),
    ("x86", "vdivps ymm0, ymm1, ymm2", "fp-div-sqrt"),
    ("x86", "rep cmpsb byte ptr [rsi], byte ptr es:[rdi]", "rep-string-cmp"),
    ("x86", "repe scasb al, byte ptr es:[rdi]", "rep-string-cmp"),
    ("x86", "vpgatherdd ymm0, ymmword ptr [rax + 4*ymm1], ymm2", "gather"),
    # Not on Intel's list, so reported even though no denylist names them.
    ("x86", "popcnt ecx, eax", "non-doit:popcnt"),
    ("x86", "tzcnt ecx, eax", "non-doit:tzcnt"),
    ("x86", "rep stosq qword ptr es:[rdi], rax", "non-doit:rep_stosq"),
    ("x86", "lock cmpxchg qword ptr [rdi], rsi", "non-doit:cmpxchg"),
    # On the list, possibly under another spelling.
    ("x86", "shl rax, cl", None),
    ("x86", "imul rax, rbx", None),
    ("x86", "cmove ecx, eax", None),
    ("x86", "cmovae ecx, eax", None),
    ("x86", "sete al", None),
    ("x86", "movabs rax, 0x123456789", None),
    ("x86", "rep movsb byte ptr es:[rdi], byte ptr [rsi]", None),
    ("x86", "movsd dword ptr es:[rdi], dword ptr [rsi]", None),
    ("x86", "vpmullw ymm3, ymm2, ymm1", None),
    ("x86", "nop word ptr cs:[rax + rax]", None),
    # In X86_EXTRA, or a branch.
    ("x86", "jne 0x40", None),
    ("x86", "movsd xmm0, qword ptr [rax]", None),
    ("x86", "vxorps xmm0, xmm0, xmm0", None),
    # FP-domain shuffles kopis no longer emits, so no longer excused.
    ("x86", "vshufps ymm0, ymm0, ymm1, 0x88", "non-doit:vshufps"),
    ("x86", "vunpcklpd ymm0, ymm0, ymm1", "non-doit:vunpcklpd"),
    ("x86", "R_X86_64_PLT32 __udivti3-0x4", "div-libcall"),
    ("x86", "R_X86_64_PLT32 __umodti3-0x4", "div-libcall"),
    ("x86", "R_X86_64_PLT32 memcpy-0x4", None),

    ("aarch64", "udiv w8, w9, w10", "int-div"),
    ("aarch64", "sdiv x0, x1, x2", "int-div"),
    ("aarch64", "fdiv d0, d1, d2", "fp-div-sqrt"),
    ("aarch64", "fsqrt s0, s1", "fp-div-sqrt"),
    # Not on Arm's list, so reported even though no denylist names them.
    ("aarch64", "fneg v0.2d, v0.2d", "non-dit:fneg"),
    ("aarch64", "fadd d0, d1, d2", "non-dit:fadd"),
    ("aarch64", "sqxtn v0.4h, v1.4s", "non-dit:sqxtn"),
    ("aarch64", "fmov d0, #1.00000000", "non-dit:fmov"),
    ("aarch64", "fmov s0, s1", "non-dit:fmov"),
    # On the list, possibly under an alias llvm-objdump keeps.
    ("aarch64", "madd x0, x1, x2, xzr", None),
    ("aarch64", "umulh x0, x1, x2", None),
    ("aarch64", "csinc w0, wzr, wzr, ne", None),
    ("aarch64", "cnt v0.8b, v1.8b", None),
    ("aarch64", "eor3 v0.16b, v1.16b, v2.16b, v3.16b", None),
    ("aarch64", "sqdmulh v0.8h, v1.8h, v2.8h", None),
    ("aarch64", "ldr q0, [x0, #0x10]", None),
    ("aarch64", "lsl w0, w0, #16", None),
    ("aarch64", "lsr x8, x9, x10", None),
    ("aarch64", "ubfiz x9, x8, #3, #3", None),
    ("aarch64", "mov h1, v1.h[1]", None),
    ("aarch64", "mov w8, v0.s[1]", None),
    # In AARCH64_EXTRA, or a branch.
    ("aarch64", "b.ne 0x40", None),
    ("aarch64", "ret", None),
    ("aarch64", "mov w8, #0x1234               // =4660", None),
    ("aarch64", "movi v0.2d, #0000000000000000", None),
    ("aarch64", "fmov d0, x8", None),
    ("aarch64", "fmov x14, d0", None),
    ("aarch64", "R_AARCH64_CALL26 __udivti3", "div-libcall"),
    ("aarch64", "R_AARCH64_CALL26 __divti3", "div-libcall"),

    ("arm", "udiv r0, r1, r2", "int-div"),
    # Conditional forms: a plain `a / b` on thumbv7em compiles to `udivne` inside an IT block.
    ("arm", "udivne r0, r0, r1", "int-div"),
    ("arm", "sdiveq r0, r1, r2", "int-div"),
    ("arm", "vdiv.f32 s0, s1, s2", "fp-div-sqrt"),
    ("arm", "vdivne.f32 s0, s1, s2", "fp-div-sqrt"),
    # Long multiply early-terminates on Cortex-M3, but this crate does not claim constant time
    # there and does not scan thumbv7m. On the thumbv7em it does target, UMULL is single-cycle.
    # If this case ever starts reporting, someone has re-added the category by accident.
    ("arm", "umull r0, r1, r2, r3", None),
    ("arm", "muls r0, r1", None),
    ("arm", "lsls r0, r1, #2", None),
    ("arm", "R_ARM_THM_CALL __aeabi_uldivmod", "div-libcall"),
    ("arm", "R_ARM_THM_CALL __aeabi_idivmod", "div-libcall"),
    ("arm", "R_ARM_THM_CALL __aeabi_memcpy", None),
]

# Symbols that must never be covered by an allowlist entry. If one is, someone has written a
# pattern broad enough to hide a finding in the code that actually touches secrets.
ALLOWLIST_MUST_NOT_COVER = [
    "kopis::kem::decap",
    "kopis::pke::decrypt",
    "kopis::sample::cbd",
    "kopis::arithmetic::ntt_crt::inv_ntt",
    "kopis::backend::avx2::keccak::xof4",
]

# A 32-bit divide, because that is the width every target we scan has a hardware divide for, and
# the narrowest one that is not: 64-bit on 32-bit Arm (`__aeabi_uldivmod`), 128-bit on the 64-bit
# targets (`__udivti3`). Thumb inlines a 128-bit divide as a loop rather than calling out.
PLANTED_SRC = """#![no_std]
#[no_mangle]
pub extern "C" fn kopis_ct_planted_divide(a: u32, b: u32) -> u32 {
    a / b
}
#[no_mangle]
pub extern "C" fn kopis_ct_planted_libcall64(a: u64, b: u64) -> u64 {
    a / b
}
#[no_mangle]
pub extern "C" fn kopis_ct_planted_libcall128(a: u128, b: u128) -> u128 {
    a / b
}
"""


def selftest(objdump: str, allowlist) -> int:
    import tempfile

    failures = []

    # 1. The matchers still classify what they are supposed to, and stay quiet otherwise.
    for fam, text, want in MATCHER_CASES:
        target = {"x86": "x86_64-unknown-linux-gnu", "aarch64": "aarch64-unknown-none",
                  "arm": "thumbv7em-none-eabi"}[fam]
        got = [n for n, _ in classifier(fam, target)(text)]
        if want is None and got:
            failures.append(f"{fam}: {text!r} should not be flagged, but matched {got}")
        elif want is not None and want not in got:
            failures.append(f"{fam}: {text!r} should be flagged as {want}, but matched {got or 'nothing'}")
    print(f"  matchers:   {len(MATCHER_CASES)} cases, "
          f"{len(MATCHER_CASES) - len(failures)} passed")

    # 2. No allowlist entry is broad enough to cover the crate's secret-handling code.
    before = len(failures)
    for sym in ALLOWLIST_MUST_NOT_COVER:
        for cat, pattern, why in allowlist:
            if pattern in sym:
                failures.append(f"allowlist entry [{cat}] {pattern!r} would cover {sym!r} ({why})")
    print(f"  allowlist:  {len(ALLOWLIST_MUST_NOT_COVER)} sensitive symbols, "
          f"{len(failures) - before} covered by an allowlist entry")

    # 3. End to end: compile a real divide for each target and require the scan to report it.
    # This is what catches a disassembler whose output format moved, or one that silently emits
    # nothing for an architecture it was not built for.
    before = len(failures)
    checked = 0
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp) / "planted.rs"
        src.write_text(PLANTED_SRC)
        for label, target, _backend, _flags in configs(host_target(), installed_targets()):
            fam = arch_family(target)
            obj = Path(tmp) / f"planted-{label.replace('/', '-')}.o"
            proc = subprocess.run(
                ["rustc", "--edition", "2021", "--crate-type", "rlib", "-O",
                 "--target", target, "--emit", f"obj={obj}", str(src)],
                capture_output=True, text=True,
            )
            if proc.returncode != 0:
                failures.append(f"{label}: could not compile the planted divide\n{proc.stderr}")
                continue
            rows, total = disassemble(objdump, [str(obj)], fam)
            checked += 1
            classify = classifier(fam, target)
            libcall = "planted_libcall64" if fam == "arm" else "planted_libcall128"
            for want, fn in [("int-div", "planted_divide"), ("div-libcall", libcall)]:
                hit = any(
                    name == want and fn in sym
                    for sym, text in rows
                    for name, _ in classify(text)
                )
                if not hit:
                    failures.append(
                        f"{label}: the planted {want} was NOT reported "
                        f"({total} instructions disassembled). The scan would pass vacuously here."
                    )
    print(f"  end-to-end: {checked} target(s), {len(failures) - before} missed a planted "
          f"divide or divide libcall")

    if failures:
        print("\nFAIL: the instruction scan is not working as intended:\n")
        for f in failures:
            print(f"  {f}")
        return 1
    print("\nPASS: the instruction scan detects planted variable-latency instructions")
    return 0


def main():
    # `--selftest` is the one thing this script needs to be told; ct-check.sh passes it through
    # for phase 2's negative control. Everything else it needs is a constant above.
    argv = sys.argv[1:]
    if argv not in ([], ["--selftest"]):
        raise SystemExit("usage: scan-instrs.py [--selftest]   (normally run via ./ct-check.sh)")

    objdump = find_llvm_objdump()
    allow = load_allowlist(ALLOWLIST)
    host = host_target()

    if argv == ["--selftest"]:
        print(f"==> instruction-scan self-test (llvm-objdump: {objdump})")
        return selftest(objdump, allow)

    print(f"==> scanning for variable-latency instructions (llvm-objdump: {objdump})")
    cfgs = configs(host, installed_targets())
    if not cfgs:
        raise SystemExit("scan-instrs: no scannable configurations")

    findings, scanned = [], []
    used = set()
    for label, target, backend, flags in cfgs:
        fam = arch_family(target)
        classify = classifier(fam, target)
        rlibs = build(target, flags)
        rows, total = disassemble(objdump, rlibs, fam)
        if total < MIN_PLAUSIBLE_INSNS:
            raise SystemExit(
                f"scan-instrs: {label} disassembled to only {total} instructions, which cannot be "
                f"right.\n  The scan would pass vacuously, so this is an error. Check that "
                f"{objdump}\n  supports {fam} and that the build produced code."
            )
        allowed = 0
        for sym, text in rows:
            for name, desc in classify(text):
                # Matched a variable-latency category. Either the allowlist says the operands are
                # public, in which case it only gets counted, or it is a finding.
                covering = [(a_cat, a_sym) for a_cat, a_sym, _ in allow
                            if a_cat == name and a_sym in sym]
                if covering:
                    used.update(covering)
                    allowed += 1
                    continue
                findings.append((label, name, desc, text, sym))
        scanned.append((label, total, allowed))

    # The third column is only ever the allowlisted hits: anything not covered by the allowlist is
    # a finding, and is printed in full below rather than folded into a count.
    print("\n    config                instructions   allowlisted")
    for label, total, allowed in scanned:
        print(f"    {label:<19} {total:>12}   {allowed:>11}")

    # Error if the allowlist contains stale entries
    unused = [(c, a) for c, a, _ in allow if (c, a) not in used]
    if unused and len(cfgs) == len(all_configs(host)):
        print(f"\nFAIL: {len(unused)} allowlist entr(y/ies) matched nothing; remove them:\n")
        for cat, pattern in unused:
            print(f"  {cat} | {pattern}")
        return 1
    elif unused:
        print(f"\nnote: {len(unused)} allowlist entr(y/ies) matched nothing, but some "
              "configurations were skipped, so they may be needed there")

    # Likewise the per-family extras, once every configuration of that family has run.
    for fam, (_, extra, *_rest) in ALLOWLISTED.items():
        fam_cfgs = [c for c in all_configs(host) if arch_family(c[1]) == fam]
        ran = [c for c in cfgs if arch_family(c[1]) == fam]
        unused_extra = sorted(set(extra) - EXTRA_USED[fam])
        if ran and len(ran) == len(fam_cfgs) and unused_extra:
            print(f"\nFAIL: {len(unused_extra)} {fam.upper()}_EXTRA entr(y/ies) matched nothing; "
                  "remove them:\n")
            for m in unused_extra:
                print(f"  {m}")
            return 1

    if findings:
        print(f"\nFAIL: {len(findings)} variable-latency instruction(s) not in the allowlist:\n")
        for label, name, desc, text, sym in findings:
            print(f"  [{label}] {name}: {text}")
            print(f"      in {sym}")
            print(f"      {desc}")
        print("\nIf the operands are public, add a line to "
              f"{ALLOWLIST.relative_to(REPO)} saying why. If a non-doit/non-dit instruction is "
              "data-independent everywhere, add it to X86_EXTRA / AARCH64_EXTRA instead.")
        return 1

    print("\nPASS: no unexpected variable-latency instructions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
