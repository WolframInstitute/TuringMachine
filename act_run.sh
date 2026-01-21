#!/bin/bash
# act_run.sh - Run GitHub Actions locally using act

set -e

# Generate entitlement ID dynamically
ENTITLEMENT_ID=$(wolframscript -c 'CreateLicenseEntitlement[]["EntitlementID"]' | tail -n 1)
echo "Using Entitlement ID: $ENTITLEMENT_ID"

# Create artifacts directory
mkdir -p ./act-artifacts

# Run act
# -P: Use wolframengine image
# -s: Pass entitlement ID secret
# --container-options: Force linux/amd64 platform
# --bind: Mount artifacts directory so we can copy files out manually
# --env ACT=true: Tell workflow to skip cache/upload steps
act \
  -P ubuntu-latest=wolframresearch/wolframengine:latest \
  -s WOLFRAMSCRIPT_ENTITLEMENTID="$ENTITLEMENT_ID" \
  --container-options "--platform linux/amd64" \
  --bind \
  --env ACT=true

# Manually find and copy the artifact since we skipped the upload step
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
