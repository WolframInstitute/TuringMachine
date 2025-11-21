docker build -t turingmachine-search .
docker run --rm -it --env-file .env -v $PWD:/opt/turingmachinesearch/TuringMachineSearch turingmachine-search wolframscript -code '<<docker_build.wl'