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
VARIANT=all
OPS=()
GEN_SUPP=0
VERBOSE=0
SELFTEST=0
MARCH=""

usage() {
    cat <<'EOF'
usage: ./ct-check.sh [OPTIONS] [OP...]

  OP                    keygen | encap | decap          (default: all three)

  --backend BACKEND     serial | avx2 | neon | native   (default: native)
                        `native` builds for this CPU with runtime backend detection, i.e. what a
                        normal `cargo build` here produces. The others pin one backend; `serial`
                        is the portable code that gets extracted to Lean, and is the only one
                        that can be checked on any machine.
  --variant V           512 | 768 | 1024 | all          (default: all)
  --march FLAGS         rustc codegen flags picking the target ISA. Defaults to
                        `-C target-cpu=x86-64-v3` on x86-64 and `-C target-feature=+neon,+sha3`
                        on AArch64. Do NOT default this to `target-cpu=native`: on a recent CPU
                        LLVM emits GFNI/AVX-512 instructions that Valgrind cannot decode, and the
                        run dies with SIGILL before it checks anything.
  --selftest            run the negative control instead of the real checks: deliberately leaky
                        code that Valgrind must report. Passes only if a leak IS found, which is
                        what proves the tagging machinery is live.
  --gen-suppressions    print a Valgrind suppression stanza for every report, to paste into
                        ct-check/suppressions.supp after you have convinced yourself the leak is
                        intentional. Does not fail on findings.
  --verbose             show the build and the full Valgrind command line
  -h, --help            this message

Exit status is 0 if no unsuppressed constant-time violation was found, 1 otherwise.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --backend) BACKEND="${2:?--backend needs a value}"; shift 2 ;;
        --variant) VARIANT="${2:?--variant needs a value}"; shift 2 ;;
        --march) MARCH="${2:?--march needs a value}"; shift 2 ;;
        --selftest) SELFTEST=1; shift ;;
        --gen-suppressions) GEN_SUPP=1; shift ;;
        --verbose) VERBOSE=1; shift ;;
        -h|--help) usage; exit 0 ;;
        keygen|encap|decap) OPS+=("$1"); shift ;;
        *) echo "ct-check.sh: unrecognised argument '$1'" >&2; usage >&2; exit 2 ;;
    esac
done

if ! command -v valgrind >/dev/null 2>&1; then
    cat >&2 <<'EOF'
ct-check.sh: valgrind not found.
  Debian/Ubuntu: sudo apt install valgrind
  Fedora:        sudo dnf install valgrind valgrind-devel
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
# AVX-512 and the run aborts with SIGILL.
if [[ -z "$MARCH" ]]; then
    case "$(uname -m)" in
        x86_64|amd64) MARCH="-C target-cpu=x86-64-v3" ;;
        aarch64|arm64) MARCH="-C target-feature=+neon,+sha3" ;;
        *) MARCH="" ;;
    esac
fi

# The backend is chosen by a cfg that build.rs reads; `native` leaves it unset so build.rs does
# its usual autodetection, which is what a normal build of this crate does.
case "$BACKEND" in
    native) export RUSTFLAGS="${RUSTFLAGS:-} $MARCH" ;;
    serial|avx2|neon) export RUSTFLAGS="${RUSTFLAGS:-} $MARCH --cfg kopis_backend=\"$BACKEND\"" ;;
    *) echo "ct-check.sh: unknown backend '$BACKEND' (want serial, avx2, neon or native)" >&2; exit 2 ;;
esac

BIN=target/ct/ct-check

# Removed first, because a failed build leaves the previous run's binary in place and this script
# would otherwise happily check it and report a PASS for a configuration it never compiled.
rm -f "$BIN"

echo "==> building ct-check (backend: $BACKEND)"
BUILD_LOG="$(mktemp)"
trap 'rm -f "$BUILD_LOG"' EXIT
if cargo build --profile ct -p ct-check >"$BUILD_LOG" 2>&1; then
    if [[ $VERBOSE -eq 1 ]]; then
        cat "$BUILD_LOG"
    else
        grep -Ev '^\s*(Compiling|Finished)' "$BUILD_LOG" || true
    fi
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
if [[ $GEN_SUPP -eq 1 ]]; then
    VG+=(--gen-suppressions=all)
else
    VG+=(--suppressions=ct-check/suppressions.supp)
fi

if [[ $SELFTEST -eq 1 ]]; then
    CMD=("${VG[@]}" "$BIN" --selftest)
else
    CMD=("${VG[@]}" "$BIN" --variant "$VARIANT" "${OPS[@]+"${OPS[@]}"}")
fi
[[ $VERBOSE -eq 1 ]] && printf '==> %s\n' "${CMD[*]}"

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
        exit 0
    fi
    cat >&2 <<'EOF'
FAIL: Valgrind did not report the deliberate leak in the self-test.

Nothing is being checked, and any PASS from this script is meaningless. Usual causes: the binary
was not actually run under Valgrind, or ct-check/shim.c was compiled against headers from a
different Valgrind than the one on PATH (check VALGRIND_INCLUDE_DIR and `valgrind --version`).
EOF
    exit 1
elif [[ $GEN_SUPP -eq 1 ]]; then
    echo "suppression stanzas printed above; findings were not treated as failures"
    exit 0
elif [[ $STATUS -eq 0 ]]; then
    echo "PASS: no secret-dependent branch or memory access (backend: $BACKEND, variant: $VARIANT)"
else
    cat <<'EOF'
FAIL: Valgrind reported a secret-dependent branch or memory access.

Each report above names the operation on the executed path. "Conditional jump or move depends on
uninitialised value(s)" is a branch on a secret; "Use of uninitialised value of size N" under a
load or store is a secret-dependent memory address, i.e. a cache-timing leak. The "Uninitialised
value was created by a client request" frame points at the classify() call that tagged the input.

If a report is an intentional leak, re-run with --gen-suppressions and add the stanza to
ct-check/suppressions.supp with a comment saying why it is safe.
EOF
fi
exit $STATUS
