docker build -t turingmachine-search .

ENTITLEMENT_ID=$(wolframscript -c 'CreateLicenseEntitlement[]["EntitlementID"]' | tail -n 1)

echo "Using Entitlement ID: $ENTITLEMENT_ID"

docker run --rm -it -e WOLFRAMSCRIPT_ENTITLEMENTID="$ENTITLEMENT_ID" -v $PWD:/opt/turingmachinesearch/TuringMachineSearch turingmachine-search wolframscript -code '<<docker_build.wl'