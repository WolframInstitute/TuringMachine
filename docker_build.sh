#!/bin/bash
# docker_build.sh - Build paclet using Docker

set -e

# Always use linux/amd64 since wolframengine only provides this architecture
PLATFORM="linux/amd64"

docker build --platform "$PLATFORM" -t turingmachine-search .

ENTITLEMENT_ID=$(wolframscript -c 'CreateLicenseEntitlement[]["EntitlementID"]' | tail -n 1)
echo "Using Entitlement ID: $ENTITLEMENT_ID"

# Create local cargo cache dir if it doesn't exist
mkdir -p "$HOME/.cargo-docker-cache"

docker run --platform "$PLATFORM" --rm -it \
  -e WOLFRAMSCRIPT_ENTITLEMENTID="$ENTITLEMENT_ID" \
  -e SDKROOT=/nonexistent \
  -v "$PWD:/opt/turingmachinesearch" \
  -v "$HOME/.cargo-docker-cache:/home/wolframengine/.cargo/registry" \
  turingmachine-search \
  /bin/bash -c "./build_all_targets.sh && wolframscript -f ci_build.wl"