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
  * `libkopis.rlib` on its own holds no instantiated KEM code, because the API is const-generic.
    That is what `ct-check/probe` is for; we disassemble it alongside the kopis rlib.
"""

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_ALLOWLIST = Path(__file__).resolve().parent / "instr-allowlist.txt"

# If a disassembly yields fewer instructions than this, something went wrong with the tooling
# rather than the code being small; treat it as an error instead of a pass.
MIN_PLAUSIBLE_INSNS = 2000

# Instruction classes whose timing can depend on operand *values*, per architecture family.
# Deliberately absent, because they are constant-time on every CPU this crate targets and would
# only add noise: variable-count shifts, POPCNT/LZCNT/TZCNT/BSF/BSR (kopis calls `count_ones()` on
# secret bytes in `sample.rs` and that is fine), integer MUL/IMUL, and CMOV/CSEL.
CATEGORIES = {
    "x86": [
        ("int-div", r"^i?div[bwlq]?\b", "DIV/IDIV: latency depends on the operands", None),
        ("pext-pdep", r"^(pext|pdep)[lq]?\b",
         "BMI2: microcoded and mask-dependent on AMD Zen 1/2", None),
        ("fp-div-sqrt", r"^(v?div[sp][sd]|v?sqrt)",
         "FP divide/sqrt: variable latency, plus subnormal penalties", None),
        ("rep-string-cmp", r"^rep[a-z]*\s+(cmps|scas)",
         "REP CMPS/SCAS: terminates early depending on the data", None),
        ("gather", r"^v?p?gather", "Gather: timing follows the address pattern", None),
    ],
    "aarch64": [
        ("int-div", r"^[us]div\b",
         "UDIV/SDIV: early-terminating on Cortex-A and Neoverse", None),
        ("fp-div-sqrt", r"^(fdiv|fsqrt)\b", "FP divide/sqrt: variable latency", None),
    ],
    # A32/T32. Long multiply is deliberately absent: `UMULL` and friends early-terminate on
    # Cortex-M3 and below, but the crate does not claim constant time on those cores, and on the
    # Cortex-M4/M7 that `thumbv7em` targets the multiply is single-cycle.
    "arm": [
        ("int-div", r"^[us]div[a-z]*\b",
         "UDIV/SDIV: early-terminating on Cortex-M (suffix allows IT-block forms like `udivne`)",
         None),
        ("fp-div-sqrt", r"^(vdiv|vsqrt)[a-z]*", "FP divide/sqrt: variable latency", None),
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


def categories_for(fam: str, target: str):
    """The compiled categories that apply to one target."""
    return [
        (name, re.compile(pattern), desc)
        for name, pattern, desc, only_on in CATEGORIES[fam]
        if only_on is None or re.match(only_on, target)
    ]


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


def configs(host: str, installed: set):
    """Every (label, target, backend, rustflags) worth scanning on this machine."""
    out = []
    fam = arch_family(host)
    if fam == "x86":
        out.append(("host/serial", host, 'serial', '--cfg kopis_backend="serial"'))
        out.append(("host/avx2", host, "avx2",
                    '-C target-feature=+avx2 --cfg kopis_backend="avx2"'))
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
    for label, target, backend, flags in cross:
        if target == host:
            continue
        if target in installed:
            out.append((label, target, backend, flags))
        else:
            print(f"  skipping {label}: target {target} not installed "
                  f"(`rustup target add {target}`)")
    return out


def build(target: str, rustflags: str) -> list:
    """Builds the probe for one configuration; returns the rlibs holding kopis code."""
    env = {**__import__("os").environ, "RUSTFLAGS": rustflags}
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
        if msg.get("target", {}).get("name") not in ("kopis", "ct-scan-probe"):
            continue
        rlibs += [f for f in msg.get("filenames", []) if f.endswith(".rlib")]
    return rlibs


def disassemble(objdump: str, rlibs: list):
    """Yields (symbol, instruction-text) and the total instruction count."""
    proc = subprocess.run([objdump, "-d", "--demangle", "--no-show-raw-insn", *rlibs],
                          capture_output=True, text=True)
    sym, total, rows = None, 0, []
    for line in proc.stdout.splitlines():
        header = re.match(r"^[0-9a-f]+ <(.+)>:", line)
        if header:
            sym = header.group(1)
            continue
        insn = re.match(r"^\s*[0-9a-f]+:\s+(\S.*)$", line)
        if not insn or sym is None:
            continue
        total += 1
        rows.append((sym, " ".join(insn.group(1).split())))
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
    ("x86", "divl %ecx", "int-div"),
    ("x86", "idivq %rbx", "int-div"),
    ("x86", "divb %r14b", "int-div"),
    ("x86", "pextq %rax, %rbx, %rcx", "pext-pdep"),
    ("x86", "pdep %edx, %ecx, %eax", "pext-pdep"),
    ("x86", "divss %xmm1, %xmm0", "fp-div-sqrt"),
    ("x86", "vsqrtpd %ymm1, %ymm0", "fp-div-sqrt"),
    ("x86", "sqrtsd %xmm1, %xmm0", "fp-div-sqrt"),
    ("x86", "vdivps %ymm2, %ymm1, %ymm0", "fp-div-sqrt"),
    ("x86", "rep cmpsb %es:(%rdi), %ds:(%rsi)", "rep-string-cmp"),
    ("x86", "repz scasb %es:(%rdi), %al", "rep-string-cmp"),
    ("x86", "vpgatherdd %ymm2, (%rax,%ymm1,4), %ymm0", "gather"),
    # Constant-time on every x86 this crate targets; flagging them would be noise.
    ("x86", "popcntl %eax, %ecx", None),
    ("x86", "shlq %cl, %rax", None),
    ("x86", "imulq %rbx, %rax", None),
    ("x86", "cmovel %eax, %ecx", None),
    ("x86", "tzcntl %eax, %ecx", None),
    ("x86", "vpmullw %ymm1, %ymm2, %ymm3", None),

    ("aarch64", "udiv w8, w9, w10", "int-div"),
    ("aarch64", "sdiv x0, x1, x2", "int-div"),
    ("aarch64", "fdiv d0, d1, d2", "fp-div-sqrt"),
    ("aarch64", "fsqrt s0, s1", "fp-div-sqrt"),
    ("aarch64", "mul x0, x1, x2", None),
    ("aarch64", "umulh x0, x1, x2", None),
    ("aarch64", "csel x0, x1, x2, eq", None),
    ("aarch64", "cnt v0.8b, v1.8b", None),
    ("aarch64", "eor3 v0.16b, v1.16b, v2.16b, v3.16b", None),

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

# A 32-bit divide, because that is the width every target we scan has a hardware divide for.
# (A 64-bit one becomes a `__aeabi_uldivmod` libcall on thumb and would never appear as `udiv`.)
PLANTED_SRC = """#![no_std]
#[no_mangle]
pub extern "C" fn kopis_ct_planted_divide(a: u32, b: u32) -> u32 {
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
        got = [n for n, rx, _ in categories_for(fam, target) if rx.match(text)]
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
            rows, total = disassemble(objdump, [str(obj)])
            hit = any(
                name == "int-div" and rx.match(text) and "planted" in sym
                for sym, text in rows
                for name, rx, _ in categories_for(fam, target)
            )
            checked += 1
            if not hit:
                failures.append(
                    f"{label}: the planted divide was NOT reported "
                    f"({total} instructions disassembled). The scan would pass vacuously here."
                )
    print(f"  end-to-end: {checked} target(s), {checked - (len(failures) - before)} reported "
          f"the planted divide")

    if failures:
        print("\nFAIL: the instruction scan is not working as intended:\n")
        for f in failures:
            print(f"  {f}")
        return 1
    print("\nPASS: the instruction scan detects planted variable-latency instructions")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--allowlist", type=Path, default=DEFAULT_ALLOWLIST)
    ap.add_argument("--list-unfiltered", action="store_true",
                    help="report allowlisted hits too, instead of only new ones")
    ap.add_argument("--selftest", action="store_true",
                    help="negative control: plant variable-latency instructions and require the "
                         "scan to find them, instead of scanning the crate")
    args = ap.parse_args()

    objdump = find_llvm_objdump()
    allow = load_allowlist(args.allowlist)
    host = host_target()

    if args.selftest:
        print(f"==> instruction-scan self-test (llvm-objdump: {objdump})")
        return selftest(objdump, allow)

    print(f"==> scanning for variable-latency instructions (llvm-objdump: {objdump})")
    cfgs = configs(host, installed_targets())
    if not cfgs:
        raise SystemExit("scan-instrs: no scannable configurations")

    findings, scanned = [], []
    for label, target, backend, flags in cfgs:
        fam = arch_family(target)
        cats = categories_for(fam, target)
        rlibs = build(target, flags)
        rows, total = disassemble(objdump, rlibs)
        if total < MIN_PLAUSIBLE_INSNS:
            raise SystemExit(
                f"scan-instrs: {label} disassembled to only {total} instructions, which cannot be "
                f"right.\n  The scan would pass vacuously, so this is an error. Check that "
                f"{objdump}\n  supports {fam} and that the build produced code."
            )
        hits = 0
        for sym, text in rows:
            for name, rx, desc in cats:
                if not rx.match(text):
                    continue
                hits += 1
                if any(a_cat == name and a_sym in sym for a_cat, a_sym, _ in allow):
                    if args.list_unfiltered:
                        print(f"    allowed  [{name}] {text}  in {sym}")
                    continue
                findings.append((label, name, desc, text, sym))
        scanned.append((label, total, hits))

    print("\n    config              instructions   flagged")
    for label, total, hits in scanned:
        print(f"    {label:<18}  {total:>10}   {hits:>7}")

    if findings:
        print(f"\nFAIL: {len(findings)} variable-latency instruction(s) not in the allowlist:\n")
        for label, name, desc, text, sym in findings:
            print(f"  [{label}] {name}: {text}")
            print(f"      in {sym}")
            print(f"      {desc}")
        print("\nIf the operands are public, add a line to "
              f"{args.allowlist.relative_to(REPO)} saying why.")
        return 1

    print("\nPASS: no unexpected variable-latency instructions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
