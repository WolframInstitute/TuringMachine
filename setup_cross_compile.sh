#!/bin/bash
# setup_cross_compile.sh - Install cacheable cross-compilation tools (Zig, libiconv)
# apt packages are installed separately (not cacheable in CI containers)

set -e

# Install Zig
echo "Installing Zig..."
mkdir -p /opt/zig
curl -L "https://ziglang.org/download/0.13.0/zig-linux-x86_64-0.13.0.tar.xz" | tar -xJ -C /opt/zig --strip-components=1
export PATH="/opt/zig:$PATH"

# Cross-compile libiconv for macOS
echo "Cross-compiling libiconv for macOS..."
mkdir -p /tmp/libiconv-build && cd /tmp/libiconv-build
curl -L "https://ftp.gnu.org/pub/gnu/libiconv/libiconv-1.17.tar.gz" | tar -xz --strip-components=1

mkdir -p build-x86_64 && cd build-x86_64
CC="zig cc -target x86_64-macos" LD="zig cc -target x86_64-macos" AR="zig ar" RANLIB="zig ranlib" \
  ../configure --host=x86_64-apple-darwin --prefix=/opt/macos-sysroot/x86_64 --disable-shared --enable-static
make -j$(nproc) && make install
cd ..

mkdir -p build-aarch64 && cd build-aarch64
CC="zig cc -target aarch64-macos" LD="zig cc -target aarch64-macos" AR="zig ar" RANLIB="zig ranlib" \
  ../configure --host=aarch64-apple-darwin --prefix=/opt/macos-sysroot/aarch64 --disable-shared --enable-static
make -j$(nproc) && make install
cd / && rm -rf /tmp/libiconv-build

echo "Cross-compilation setup complete!"
