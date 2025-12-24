# Base image: Official Wolfram Engine
FROM wolframresearch/wolframengine:latest

# Non-interactive apt
ENV DEBIAN_FRONTEND=noninteractive

# Switch to root for installations
USER root

# Install apt dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl ca-certificates build-essential pkg-config libssl-dev git \
    uuid-dev lld \
    mingw-w64 \
    gcc-aarch64-linux-gnu \
    libc6-dev-arm64-cross \
    gcc-x86-64-linux-gnu \
    && rm -rf /var/lib/apt/lists/* \
    && ln -sf /usr/bin/x86_64-linux-gnu-gcc /usr/bin/x86_64-unknown-linux-gnu-gcc \
    && ln -sf /usr/bin/aarch64-linux-gnu-gcc /usr/bin/aarch64-unknown-linux-gnu-gcc

WORKDIR /opt/turingmachinesearch

# Copy and run cross-compilation setup (Zig, libiconv)
COPY zcc setup_cross_compile.sh ./
RUN chmod +x setup_cross_compile.sh && ./setup_cross_compile.sh
RUN cp zcc /usr/local/bin/zcc && chmod +x /usr/local/bin/zcc
ENV PATH="/opt/zig:${PATH}"

# Switch to wolframengine user for Rust installation
USER wolframengine
WORKDIR /home/wolframengine

# Copy and run Rust setup
COPY --chown=wolframengine:wolframengine setup_rust.sh ./
RUN chmod +x setup_rust.sh && ./setup_rust.sh
ENV PATH="/home/wolframengine/.cargo/bin:${PATH}"

# Add CC env var for host build scripts
ENV CC_x86_64_unknown_linux_gnu=gcc

WORKDIR /opt/turingmachinesearch

ARG WOLFRAMSCRIPT_ENTITLEMENTID
ENV WOLFRAMSCRIPT_ENTITLEMENTID=${WOLFRAMSCRIPT_ENTITLEMENTID}

COPY --chown=wolframengine:wolframengine ci_build.wl ./ci_build.wl