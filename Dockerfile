# Base image: Official Wolfram Engine
FROM wolframresearch/wolframengine:latest

# Non-interactive apt
ENV DEBIAN_FRONTEND=noninteractive

# Install build dependencies:
# - build-essential, curl, git, pkg-config, libssl-dev, uuid-dev, lld (common)
# - mingw-w64 (Windows cross-compilation)
# - gcc-aarch64-linux-gnu (Linux ARM64 cross-compilation)
USER root
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl ca-certificates build-essential pkg-config libssl-dev git \
    uuid-dev lld \
    mingw-w64 \
    gcc-aarch64-linux-gnu \
    libc6-dev-arm64-cross \
    gcc-x86-64-linux-gnu \
    && rm -rf /var/lib/apt/lists/* && \
    ln -s /usr/bin/x86_64-linux-gnu-gcc /usr/bin/x86_64-unknown-linux-gnu-gcc && \
    ln -s /usr/bin/aarch64-linux-gnu-gcc /usr/bin/aarch64-unknown-linux-gnu-gcc

# Install Zig (for macOS cross-compilation) - Install as root to /opt
RUN mkdir -p /opt/zig && \
    curl -L "https://ziglang.org/download/0.13.0/zig-linux-x86_64-0.13.0.tar.xz" | tar -xJ -C /opt/zig --strip-components=1
ENV PATH="/opt/zig:${PATH}"

# Cross-compile libiconv for macOS targets using Zig
# This is needed because Zig's macOS sysroot doesn't include libiconv
RUN mkdir -p /tmp/libiconv-build && cd /tmp/libiconv-build && \
    curl -L "https://ftp.gnu.org/pub/gnu/libiconv/libiconv-1.17.tar.gz" | tar -xz --strip-components=1 && \
    # Build for x86_64-macos
    mkdir -p build-x86_64 && cd build-x86_64 && \
    CC="zig cc -target x86_64-macos" \
    AR="zig ar" \
    RANLIB="zig ranlib" \
    ../configure --host=x86_64-apple-darwin --prefix=/opt/macos-sysroot/x86_64 --disable-shared --enable-static && \
    make -j$(nproc) && make install && \
    cd .. && \
    # Build for aarch64-macos
    mkdir -p build-aarch64 && cd build-aarch64 && \
    CC="zig cc -target aarch64-macos" \
    AR="zig ar" \
    RANLIB="zig ranlib" \
    ../configure --host=aarch64-apple-darwin --prefix=/opt/macos-sysroot/aarch64 --disable-shared --enable-static && \
    make -j$(nproc) && make install && \
    cd / && rm -rf /tmp/libiconv-build

# Copy zcc wrapper script (filters unsupported macOS linker flags)
COPY zcc /usr/local/bin/zcc
RUN chmod +x /usr/local/bin/zcc

# Switch to wolframengine user for Rust installation
USER wolframengine
WORKDIR /home/wolframengine

# Install Rust toolchain (stable) for wolframengine user
RUN curl -fsSL https://sh.rustup.rs -o rustup.sh && \
    sh rustup.sh -y --default-toolchain stable && \
    rm rustup.sh

# Add Cargo to PATH for subsequent Run commands and for the image
ENV PATH="/home/wolframengine/.cargo/bin:${PATH}"

# Add targets
RUN rustup target add \
    x86_64-unknown-linux-gnu \
    aarch64-unknown-linux-gnu \
    x86_64-pc-windows-gnu \
    x86_64-apple-darwin \
    aarch64-apple-darwin

# Install rustfmt
RUN rustup component add rustfmt

# Add CC env var to force usage of gcc for host build scripts (fixing x86_64-unknown-linux-gnu-gcc not found)
ENV CC_x86_64_unknown_linux_gnu=gcc

# Configure Cargo global config for linkers in ~/.cargo/config.toml
# Note: Zig target triples should be 'x86_64-macos' and 'aarch64-macos' (no gnu suffix)
# Using 'zcc' wrapper as linker to ensure 'zig cc' is invoked.
# Added -L paths for cross-compiled libiconv
RUN mkdir -p /home/wolframengine/.cargo && \
    echo '[target.x86_64-apple-darwin]\nlinker = "zcc"\nrustflags = ["-C", "link-arg=-target", "-C", "link-arg=x86_64-macos", "-C", "link-arg=-L/opt/macos-sysroot/x86_64/lib"]\n\n[target.aarch64-apple-darwin]\nlinker = "zcc"\nrustflags = ["-C", "link-arg=-target", "-C", "link-arg=aarch64-macos", "-C", "link-arg=-L/opt/macos-sysroot/aarch64/lib"]\n\n[target.x86_64-pc-windows-gnu]\nlinker = "x86_64-w64-mingw32-gcc"\n\n[target.aarch64-unknown-linux-gnu]\nlinker = "aarch64-linux-gnu-gcc"\n\n[target.x86_64-unknown-linux-gnu]\nlinker = "x86_64-linux-gnu-gcc"' > /home/wolframengine/.cargo/config.toml

WORKDIR /opt/turingmachinesearch

ARG WOLFRAMSCRIPT_ENTITLEMENTID
ENV WOLFRAMSCRIPT_ENTITLEMENTID=${WOLFRAMSCRIPT_ENTITLEMENTID}

COPY --chown=wolframengine:wolframengine docker_build.wl ./docker_build.wl