# Base image: Official Wolfram Engine
FROM wolframresearch/wolframengine:latest

# Non-interactive apt
ENV DEBIAN_FRONTEND=noninteractive

# Install build dependencies for Rust + native linking
USER root
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl ca-certificates build-essential pkg-config libssl-dev git \
    uuid-dev lld \
    && rm -rf /var/lib/apt/lists/*


# Install Rust toolchain (stable) for all users
RUN curl -fsSL https://sh.rustup.rs -o /tmp/rustup.sh && \
    sh /tmp/rustup.sh -y --default-toolchain stable --no-modify-path && \
    rm /tmp/rustup.sh && \
    /root/.cargo/bin/rustup component add rustfmt && \
    mkdir -p /opt/rust/cargo && \
    cp -r /root/.cargo/* /opt/rust/cargo/ && \
    chown -R wolframengine:wolframengine /opt/rust/cargo
ENV PATH="/opt/rust/cargo/bin:${PATH}"

USER wolframengine
WORKDIR /opt/turingmachinesearch

RUN rustup default stable

ARG WOLFRAMSCRIPT_ENTITLEMENTID
ENV WOLFRAMSCRIPT_ENTITLEMENTID=${WOLFRAMSCRIPT_ENTITLEMENTID}

COPY docker_build.wl ./docker_build.wl