#!/bin/bash

set -eux

REPO_ROOT="$(cd "$(dirname "$0")" && pwd)"

# The aeneas version we use is dictated by AENEAS_VERSION.txt in the crate root
AENEAS_VERSION="$(tr -d '[:space:]' < "${REPO_ROOT}/AENEAS_VERSION.txt")"
# Place to save aeneas and charon prebuilt binaries
BIN_DIR="${REPO_ROOT}/.aeneas-bin/${AENEAS_VERSION}"

# Fetch the appropriate aeneas/charon prebuilt binaries from Github, and cache them locally
case "$(uname -s)-$(uname -m)" in
    Linux-x86_64)               AENEAS_ASSET="aeneas-linux-x86_64.tar.gz" ;;
    Linux-aarch64 | Linux-arm64) AENEAS_ASSET="aeneas-linux-aarch64.tar.gz" ;;
    Darwin-arm64)               AENEAS_ASSET="aeneas-macos-aarch64.tar.gz" ;;
    Darwin-x86_64)              AENEAS_ASSET="aeneas-macos-x86_64.tar.gz" ;;
    *)
        echo "No prebuilt aeneas for $(uname -s)-$(uname -m)." >&2
        echo "Upstream publishes linux-{x86_64,aarch64} and macos-{x86_64,aarch64}." >&2
        exit 1
        ;;
esac
if [ ! -x "${BIN_DIR}/aeneas" ] || [ ! -x "${BIN_DIR}/charon" ]; then
    rm -rf "${BIN_DIR}"
    mkdir -p "${BIN_DIR}"
    echo "Fetching aeneas binary from Github..."
    curl -fsSL --retry 3 \
        "https://github.com/AeneasVerif/aeneas/releases/download/${AENEAS_VERSION}/${AENEAS_ASSET}" \
        | tar xz -C "${BIN_DIR}"
fi

CHARON="${BIN_DIR}/charon"
AENEAS="${BIN_DIR}/aeneas"

# We don't want Charon's build artifacts to interfere with other builds, and
# vice-versa. So we give it its own directory
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-target/charon}"


# Extract the serial backend
export RUSTFLAGS='--cfg kopis_backend="serial"'
$CHARON cargo --preset=aeneas
$AENEAS kopis.llbc -backend lean -loops-to-rec -namespace RustKopisSerial
mv Kopis.lean ./lean/ExtractedRustSerial.lean
rm kopis.llbc

# Extract the AVX2 backend. We omit extraction of our AVX2 intrinsics, since
# they're not supported by aeneas
export RUSTFLAGS='--cfg kopis_backend="avx2" -C target-feature=+avx2'
$CHARON cargo --preset=aeneas \
    --opaque 'kopis::backend::avx2::intrinsics' \
    -- --target x86_64-unknown-linux-gnu
$AENEAS kopis.llbc -backend lean -loops-to-rec -namespace RustKopisAvx2
mv Kopis.lean ./lean/ExtractedRustAvx2.lean
rm kopis.llbc

# Extract the AVX2 backend. We omit extraction of our NEON intrinsics, since
# they're not supported by aeneas
export RUSTFLAGS='--cfg kopis_backend="neon" -C target-feature=+sha3'
$CHARON cargo --preset=aeneas \
    --opaque 'kopis::backend::neon::intrinsics' \
    -- --target aarch64-unknown-linux-gnu
$AENEAS kopis.llbc -backend lean -loops-to-rec -namespace RustKopisNeon
mv Kopis.lean ./lean/ExtractedRustNeon.lean
rm kopis.llbc
