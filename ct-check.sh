#!/usr/bin/env bash
#
# Constant-time validation for the kopis crate.
#
# Builds the ct-check harness and runs it under Valgrind's Memcheck. The harness tags secret
# inputs as undefined memory; Memcheck then reports any branch or memory address that depends on
# them, which is precisely a timing side channel. See ct-check/src/lib.rs for the details.
#
# Requires Valgrind and its headers (Debian/Ubuntu: `sudo apt install valgrind`).

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

BACKEND=native
SELFTEST=0
SCAN=1
SCAN_ONLY=0

usage() {
    cat <<'EOF'
usage: ./ct-check.sh [OPTIONS]

Every parameter set and all three operations are checked on every run; there is no flag to
narrow that. A partial run makes a weaker claim while looking exactly like a full one.

Runs two phases:
  1. Valgrind: secrets are tagged as undefined memory, and any branch or memory address that
     depends on one is an error. Sound on the code path that ran, on this machine's architecture.
  2. Instruction scan: disassembles every target we can cross-compile to and looks for
     instructions whose latency depends on their operands, which phase 1 is blind to. Coarse —
     it cannot tell a secret operand from a public one — but it reaches the backends Valgrind
     cannot run here.

  --backend BACKEND     serial | avx2 | neon | native   (default: native)
                        `native` builds for this CPU with runtime backend detection, i.e. what a
                        normal `cargo build` here produces. The others pin one backend; `serial`
                        is the portable code that gets extracted to Lean, and is the only one
                        that can be checked on any machine.
  --no-scan             skip phase 2 (the instruction scan), running only the Valgrind checks.
                        Phase 2 does not depend on which backend the harness was built against,
                        so a matrix that runs this script once per backend wants it on all but
                        one of them.
  --scan-only           skip phase 1 (Valgrind), running only the instruction scan. Fast, and the
                        only phase that works without Valgrind installed.
  --selftest            run both phases' negative controls instead of the real checks. Phase 1
                        runs deliberately leaky code that Valgrind must report; phase 2 plants
                        variable-latency instructions the scan must find, and checks that no
                        allowlist entry is broad enough to cover the crate's secret-handling
                        code. Passes only if the planted problems ARE found, which is what
                        proves both phases are live rather than silently inert.
  -h, --help            this message

Exit status is 0 if no constant-time violation was found, 1 otherwise. There is no suppression
mechanism: every report counts.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --backend) BACKEND="${2:?--backend needs a value}"; shift 2 ;;
        --no-scan) SCAN=0; shift ;;
        --scan-only) SCAN_ONLY=1; shift ;;
        --selftest) SELFTEST=1; shift ;;
        -h|--help) usage; exit 0 ;;
        *) echo "ct-check.sh: unrecognised argument '$1'" >&2; usage >&2; exit 2 ;;
    esac
done

if [[ $SCAN_ONLY -eq 0 ]] && ! command -v valgrind >/dev/null 2>&1; then
    cat >&2 <<'EOF'
ct-check.sh: valgrind not found, so phase 1 cannot run.
  Debian/Ubuntu: sudo apt install valgrind
  Fedora:        sudo dnf install valgrind valgrind-devel

On macOS there is nothing to install: Valgrind has no arm64 Darwin port, and its x86 macOS
support stopped at 10.13. Phase 1 is Linux-only in practice. Phase 2 works fine there:

    ./ct-check.sh --scan-only

That checks instruction latency across every target, but does NOT track secrets, so it does not
replace phase 1. Run the full script on a Linux box before trusting a release.
EOF
    exit 2
fi

# A backend can only be checked on hardware that can run it: Valgrind interprets the guest's own
# instruction set, so there is no cross-architecture option here. Catch the impossible
# combinations before the build, where the diagnosis is obvious.
HOST_ARCH="$(uname -m)"
case "$BACKEND:$HOST_ARCH" in
    avx2:x86_64|avx2:amd64|neon:aarch64|neon:arm64|serial:*|native:*) ;;
    avx2:*)
        echo "ct-check.sh: the avx2 backend needs an x86-64 host, but this is $HOST_ARCH." >&2
        echo "  Only --backend serial can be checked here." >&2
        exit 2 ;;
    neon:*)
        echo "ct-check.sh: the neon backend needs an AArch64 host with FEAT_SHA3, but this is $HOST_ARCH." >&2
        echo "  Valgrind cannot emulate another architecture; run this script on AArch64 hardware." >&2
        exit 2 ;;
esac

# The NEON backend is compiled against the ARMv8.2 SHA3 extension, so an AArch64 CPU without it
# builds fine (the feature is forced by a codegen flag) and then dies on the first `eor3`. Say so
# up front instead.
if [[ "$BACKEND" == neon && -r /proc/cpuinfo ]] && ! grep -qw sha3 /proc/cpuinfo; then
    echo "ct-check.sh: this AArch64 CPU does not report FEAT_SHA3, which the neon backend needs." >&2
    echo "  Apple silicon and Neoverse V-series have it; Neoverse N1 (Graviton2) does not." >&2
    echo "  Use --backend serial here, which is what such a target builds by default anyway." >&2
    exit 2
fi

# Pick the ISA to compile for. This has to be wide enough that the accelerated backend is
# actually compiled in — checking only the portable code on an x86 box would miss every bug in
# the hand-written AVX2 — but no wider than Valgrind's decoder. x86-64-v3 is exactly AVX2 + BMI2
# + FMA, all of which Valgrind handles; `native` on anything newer than Ice Lake pulls in GFNI or
# AVX-512 and the run aborts with SIGILL. There is deliberately no flag to override this — a host
# that needs something else should edit the cases here, where that reasoning is written down.
case "$(uname -m)" in
    x86_64|amd64) MARCH="-C target-cpu=x86-64-v3" ;;
    aarch64|arm64) MARCH="-C target-feature=+neon,+sha3" ;;
    *) MARCH="" ;;
esac

# The backend is chosen by a cfg that build.rs reads; `native` leaves it unset so build.rs does
# its usual autodetection, which is what a normal build of this crate does.
case "$BACKEND" in
    native) export RUSTFLAGS="${RUSTFLAGS:-} $MARCH" ;;
    serial|avx2|neon) export RUSTFLAGS="${RUSTFLAGS:-} $MARCH --cfg kopis_backend=\"$BACKEND\"" ;;
    *) echo "ct-check.sh: unknown backend '$BACKEND' (want serial, avx2, neon or native)" >&2; exit 2 ;;
esac

VG_STATUS=0
SCAN_STATUS=0

if [[ $SCAN_ONLY -eq 0 ]]; then

if [[ $SELFTEST -eq 1 ]]; then
    echo "==> phase 1: valgrind negative control"
else
    echo "==> phase 1: valgrind (secret-dependent branches and memory addresses)"
fi

BIN=target/ct/ct-check

# Removed first, because a failed build leaves the previous run's binary in place and this script
# would otherwise happily check it and report a PASS for a configuration it never compiled.
rm -f "$BIN"

echo "==> building ct-check (backend: $BACKEND)"
BUILD_LOG="$(mktemp)"
trap 'rm -f "$BUILD_LOG"' EXIT
if cargo build --profile ct -p ct-check >"$BUILD_LOG" 2>&1; then
    grep -Ev '^\s*(Compiling|Finished)' "$BUILD_LOG" || true
else
    cat "$BUILD_LOG" >&2
    echo "ct-check.sh: build failed (backend: $BACKEND); nothing was checked" >&2
    exit 2
fi

[[ -x "$BIN" ]] || { echo "ct-check.sh: $BIN was not produced" >&2; exit 2; }

VG=(
    valgrind
    --tool=memcheck
    # Definedness errors only. The harness leaks its own allocations by design at exit.
    --leak-check=no
    # Names the classify() call that tagged the value, which is what turns a report into a
    # diagnosis rather than a puzzle.
    --track-origins=yes
    # Kopis inlines aggressively at -O3; a shallow trace usually stops inside the XOF.
    --num-callers=50
    --error-exitcode=1
)

if [[ $SELFTEST -eq 1 ]]; then
    CMD=("${VG[@]}" "$BIN" --selftest)
else
    CMD=("${VG[@]}" "$BIN")
fi
# Always echoed: it is the one line someone needs to reproduce a report by hand.
printf '==> %s\n' "${CMD[*]}"

echo "==> running under valgrind (this takes a couple of minutes)"
set +e
"${CMD[@]}"
STATUS=$?
set -e

echo
if [[ $SELFTEST -eq 1 ]]; then
    # Inverted: the control leaks on purpose, so silence means the tagging never took effect and
    # every other run of this script has been passing vacuously.
    if [[ $STATUS -ne 0 ]]; then
        echo "PASS: the harness detects a secret-dependent branch and a secret-dependent load"
        STATUS=0
    else
        cat >&2 <<'EOF'
FAIL: Valgrind did not report the deliberate leak in the self-test.

Nothing is being checked, and any PASS from this script is meaningless. Usual causes: the binary
was not actually run under Valgrind, or ct-check/shim.c was compiled against headers from a
different Valgrind than the one on PATH (check VALGRIND_INCLUDE_DIR and `valgrind --version`).
EOF
        STATUS=1
    fi
elif [[ $STATUS -eq 0 ]]; then
    echo "PASS: no secret-dependent branch or memory access (backend: $BACKEND)"
elif [[ $STATUS -eq 101 ]]; then
    # Valgrind passes the child's exit status through when it found no errors of its own, and 101
    # is a Rust panic: one of the checks asserted, so the operation under test is broken or was
    # optimised away. Nothing was said about constant time either way.
    cat <<'EOF'
FAIL: a check panicked before Valgrind had anything to report.

The assertion above means the operation under test did not produce the expected value — it is
either genuinely broken or no longer being executed. Fix that first; this run made no statement
about constant-time behaviour.
EOF
else
    cat <<'EOF'
FAIL: Valgrind reported a secret-dependent branch or memory access.

Each report above names the operation on the executed path. "Conditional jump or move depends on
uninitialised value(s)" is a branch on a secret; "Use of uninitialised value of size N" under a
load or store is a secret-dependent memory address, i.e. a cache-timing leak. The "Uninitialised
value was created by a client request" frame points at the classify() call that tagged the input.

Every report is a failure; there is no list of exceptions to add one to. Kopis has no intentional
leak to allowlist, and if one is ever wanted, that is a change to the design rather than a filter
on this output.
EOF
fi
VG_STATUS=$STATUS

fi  # end phase 1

if [[ $SCAN -eq 1 ]]; then
    if ! command -v python3 >/dev/null 2>&1; then
        echo "ct-check.sh: python3 is needed for the instruction scan (or pass --no-scan)" >&2
        exit 2
    fi
    echo
    if [[ $SELFTEST -eq 1 ]]; then
        echo "==> phase 2: instruction-scan negative control"
    else
        echo "==> phase 2: instruction scan (operand-dependent latency)"
    fi
    SCAN_ARGS=()
    [[ $SELFTEST -eq 1 ]] && SCAN_ARGS+=(--selftest)
    set +e
    python3 ct-check/scan-instrs.py "${SCAN_ARGS[@]+"${SCAN_ARGS[@]}"}"
    SCAN_STATUS=$?
    set -e
fi

# Name the phases that actually ran. A bare "PASS" after --scan-only reads as a clean bill for
# the whole crate when half the checking was skipped, which is the same vacuous-pass trap the
# self-test exists to catch.
if [[ $SELFTEST -eq 1 ]]; then
    COVERAGE="self-test: both phases detect a planted problem"
elif [[ $SCAN_ONLY -eq 1 ]]; then
    COVERAGE="phase 2 only — no secret tracking was performed"
elif [[ $SCAN -eq 0 ]]; then
    COVERAGE="phase 1 only — no instruction scan was performed"
else
    COVERAGE="both phases"
fi

echo
if [[ $VG_STATUS -eq 0 && $SCAN_STATUS -eq 0 ]]; then
    echo "=== ct-check: PASS ($COVERAGE) ==="
    exit 0
fi
echo "=== ct-check: FAIL ($COVERAGE) ===" >&2
if [[ $VG_STATUS -ne 0 ]]; then
    echo "  phase 1 (valgrind): secret-dependent branch or memory access" >&2
fi
if [[ $SCAN_STATUS -ne 0 ]]; then
    echo "  phase 2 (instruction scan): unexpected variable-latency instruction" >&2
fi
exit 1
