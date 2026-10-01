#!/bin/bash
# start_wl.sh - Open a shell in the paclet build container

set -e

# run from the repository root, wherever the script is called from
cd "$(dirname "$0")/.."

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