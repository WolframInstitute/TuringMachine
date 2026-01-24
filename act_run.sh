#!/bin/bash
# act_run.sh - Run GitHub Actions locally using act

set -e

WORKFLOW="${1:-build}"

# Generate entitlement ID dynamically
ENTITLEMENT_ID=$(wolframscript -c 'CreateLicenseEntitlement[]["EntitlementID"]' | tail -n 1)
RESOURCE_PUBLISHER_TOKEN=$(wolframscript -c 'PacletSymbol["Wolfram/PacletCICD", "Wolfram`PacletCICD`CreatePublisherToken"]["act"]["TokenString"]' | tail -n 1)
echo "Using Entitlement ID: $ENTITLEMENT_ID"
echo "Using Resource Publisher Token: $RESOURCE_PUBLISHER_TOKEN"

# Create artifacts directory
mkdir -p ./act-artifacts

# Determine which workflow to run
case "$WORKFLOW" in
  build)
    WORKFLOW_FILE=".github/workflows/build_paclet.yml"
    ;;
  submit)
    WORKFLOW_FILE=".github/workflows/Submit.yml"
    ;;
  *)
    echo "Usage: $0 [build|submit]"
    exit 1
    ;;
esac

echo "Running workflow: $WORKFLOW_FILE"

# Run act
# -W: Specify workflow file
# -P: Use wolframengine image
# -s: Pass secrets
# --container-architecture: Force linux/amd64 platform for M-series Macs
# --bind: Mount artifacts directory so we can copy files out manually
# --env ACT=true: Tell workflow to skip cache/upload steps
act \
  -W "$WORKFLOW_FILE" \
  -P ubuntu-latest=wolframresearch/wolframengine:latest \
  -s WOLFRAMSCRIPT_ENTITLEMENTID="$ENTITLEMENT_ID" \
  -s RESOURCE_PUBLISHER_TOKEN="$RESOURCE_PUBLISHER_TOKEN" \
  --container-architecture linux/amd64 \
  --bind \
  --env ACT=true \
  --container-options "-v act-zig-cache:/opt/zig -v act-cargo-cache:/root/.cargo -v act-rustup-cache:/root/.rustup -v act-macos-sysroot:/opt/macos-sysroot"

# For build workflow, copy artifacts
if [ "$WORKFLOW" = "build" ]; then
  echo "finding paclet..."
  PACLET=$(find . -name "*.paclet" -type f | grep "TuringMachine" | head -1)
  if [ -n "$PACLET" ]; then
      cp "$PACLET" ./act-artifacts/
      echo "Copied $PACLET to ./act-artifacts/"
  else
      echo "No paclet found to copy."
  fi

  echo ""
  echo "=== Artifacts saved to ./act-artifacts ==="
  ls -la ./act-artifacts/ 2>/dev/null || echo "No artifacts found"
fi
