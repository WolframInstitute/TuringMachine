PacletInstall["https://www.wolframcloud.com/obj/nikm/ExternalEvaluate.paclet"]
PacletInstall["https://www.wolframcloud.com/obj/nikm/PacletExtensions.paclet"]

PacletDirectoryLoad["/opt/turingmachinesearch/TuringMachineSearch"]
Needs["ExtensionCargo`"]
ExtensionCargo`CargoBuild[PacletObject["TuringMachineSearch"]]