#!/bin/bash
set -e

# Cross-compilation build script for ndtm_search.
# Builds release binaries for all supported platforms and installs each into the
# paclet's LibraryResources/<WolframSystemID>/ directory, where Kernel/Functions.wl
# loads it directly (no ExtensionCargo).

LIB="ndtm_search"
PACLET_LIBRESOURCES="TuringMachine/LibraryResources"

# Define targets: WolframSystemID:Rust_target
TARGETS=(
    "MacOSX-x86-64:x86_64-apple-darwin"
    "MacOSX-ARM64:aarch64-apple-darwin"
    "Linux-x86-64:x86_64-unknown-linux-gnu"
    "Linux-ARM64:aarch64-unknown-linux-gnu"
    "Windows-x86-64:x86_64-pc-windows-gnu"
)

echo "Building $LIB for all targets..."
echo

for entry in "${TARGETS[@]}"; do
    system_id="${entry%%:*}"
    target="${entry##*:}"
    echo "=== Building for $system_id ($target) ==="

    if ! cargo build --release --target "$target"; then
        echo "✗ $system_id build failed"
        exit 1
    fi

    # Locate the produced dynamic library and its Wolfram-facing name/extension.
    case "$target" in
        *-windows-*) src="target/$target/release/${LIB}.dll";     ext="dll"   ;;
        *-apple-*)   src="target/$target/release/lib${LIB}.dylib"; ext="dylib" ;;
        *)           src="target/$target/release/lib${LIB}.so";    ext="so"    ;;
    esac

    dstdir="$PACLET_LIBRESOURCES/$system_id"
    mkdir -p "$dstdir"
    cp "$src" "$dstdir/${LIB}.$ext"
    echo "✓ $system_id -> $dstdir/${LIB}.$ext"
    echo
done

echo "=== All builds completed and installed into $PACLET_LIBRESOURCES/<SystemID>/ ==="
