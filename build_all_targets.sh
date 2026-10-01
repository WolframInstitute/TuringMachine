#!/bin/bash
set -e

# Cross-compilation build script.
#
# `cargo wl build` (cargo-wl, from WolframResearch/wolfram-rust-library)
# compiles the ndtm_search cdylib, reads the exported-function manifest
# embedded in the host binary, and writes each platform's library together
# with its generated Functions.wl loader into
# TuringMachine/Binaries/ndtm_search-<SystemID>/ (see
# [package.metadata.wl.pacletinfo] in TuringMachine/Libs/ndtm_search/Cargo.toml).
#
# The host platform is built by the first invocation; each cross target gets
# its own invocation. Re-running for the host inside the loop is a cached
# no-op, so the host appearing in TARGETS is harmless on any machine.

TARGETS=(
    "MacOSX-x86-64:x86_64-apple-darwin"
    "MacOSX-ARM64:aarch64-apple-darwin"
    "Linux-x86-64:x86_64-unknown-linux-gnu"
    "Linux-ARM64:aarch64-unknown-linux-gnu"
    "Windows-x86-64:x86_64-pc-windows-gnu"
)

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
CRATE_DIR="$SCRIPT_DIR/TuringMachine/Libs/ndtm_search"

# wstp-sys (a hard cargo-wl dependency) needs the WSTP SDK at build time, and
# upstream wolfram-app-discovery cannot find it from an installed engine without
# an env override (WolframResearch/wolfram-rust-library#23). Point it at the
# engine's DeveloperKit when present (e.g. the wolframresearch/wolframengine CI
# image); elsewhere the glob matches nothing and the variable stays unset.
if [ -z "${WSTP_COMPILER_ADDITIONS_DIRECTORY:-}" ]; then
    for d in /usr/local/Wolfram/*/*/SystemFiles/Links/WSTP/DeveloperKit/Linux-x86-64/CompilerAdditions; do
        if [ -d "$d" ]; then
            export WSTP_COMPILER_ADDITIONS_DIRECTORY="$d"
            echo "WSTP_COMPILER_ADDITIONS_DIRECTORY=$d"
            break
        fi
    done
fi

if ! command -v cargo-wl &> /dev/null; then
    echo "=== Installing cargo-wl ==="
    cargo install cargo-wl --locked
fi

cd "$CRATE_DIR"

echo "=== Building host platform ==="
cargo wl build --release
echo

for entry in "${TARGETS[@]}"; do
    system_id="${entry%%:*}"
    echo "=== Building for $system_id ==="

    if cargo wl build --release --system-id "$system_id"; then
        echo "✓ $system_id build succeeded"
    else
        echo "✗ $system_id build failed"
        exit 1
    fi
    echo
done

echo "=== All builds completed successfully ==="

echo
echo "Built library packages:"
for entry in "${TARGETS[@]}"; do
    system_id="${entry%%:*}"
    echo "  $system_id: TuringMachine/Binaries/ndtm_search-$system_id/"
done
