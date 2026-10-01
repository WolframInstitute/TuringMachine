#!/bin/bash
# setup_rust.sh - Install Rust and configure for cross-compilation
# Used by both Dockerfile (local) and GitHub Actions (CI)

set -e

CARGO_HOME="${CARGO_HOME:-$HOME/.cargo}"

# Install Rust if not present (minimal profile to save space)
if ! command -v rustup &> /dev/null; then
    curl -fsSL https://sh.rustup.rs -o /tmp/rustup.sh
    sh /tmp/rustup.sh -y --default-toolchain stable --profile minimal
    rm /tmp/rustup.sh
fi

# Ensure cargo is in PATH
export PATH="$CARGO_HOME/bin:$PATH"

# Add targets
rustup target add \
    x86_64-unknown-linux-gnu \
    aarch64-unknown-linux-gnu \
    x86_64-pc-windows-gnu \
    x86_64-apple-darwin \
    aarch64-apple-darwin

# Install rustfmt
rustup component add rustfmt

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

# Install cargo-wl (WolframResearch/wolfram-rust-library): builds LibraryLink
# crates and generates their WL loader packages; used by build_all_targets.sh.
if ! command -v cargo-wl &> /dev/null; then
    cargo install cargo-wl --locked
fi

# Configure Cargo linkers
mkdir -p "$CARGO_HOME"
cat > "$CARGO_HOME/config.toml" << 'EOF'
[target.x86_64-apple-darwin]
linker = "zcc"
rustflags = ["-C", "link-arg=-target", "-C", "link-arg=x86_64-macos", "-C", "link-arg=-L/opt/macos-sysroot/x86_64/lib"]

[target.aarch64-apple-darwin]
linker = "zcc"
rustflags = ["-C", "link-arg=-target", "-C", "link-arg=aarch64-macos", "-C", "link-arg=-L/opt/macos-sysroot/aarch64/lib"]

[target.x86_64-pc-windows-gnu]
linker = "x86_64-w64-mingw32-gcc"

[target.aarch64-unknown-linux-gnu]
linker = "aarch64-linux-gnu-gcc"

[target.x86_64-unknown-linux-gnu]
linker = "x86_64-linux-gnu-gcc"
EOF

echo "Rust setup complete!"
