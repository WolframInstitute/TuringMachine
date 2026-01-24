#!/bin/bash
# docker_build.sh - Build paclet using Docker

set -e

# Always use linux/amd64 since wolframengine only provides this architecture
PLATFORM="linux/amd64"

docker build --platform "$PLATFORM" -t turingmachine .

ENTITLEMENT_ID=$(wolframscript -c 'CreateLicenseEntitlement[]["EntitlementID"]' | tail -n 1)
echo "Using Entitlement ID: $ENTITLEMENT_ID"


docker run --platform "$PLATFORM" --rm -it \
  -e WOLFRAMSCRIPT_ENTITLEMENTID="$ENTITLEMENT_ID" \
  -e SDKROOT=/nonexistent \
  -v "$PWD:/opt/TuringMachine" \
  turingmachine