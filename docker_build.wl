PacletInstall["https://www.wolframcloud.com/obj/nikm/ExternalEvaluate.paclet"]
PacletInstall["https://www.wolframcloud.com/obj/nikm/PacletExtensions.paclet"]

Needs["ExtensionCargo`"]

PacletDirectoryLoad["/opt/turingmachinesearch/TuringMachineSearch"]
ExtensionCargo`CargoBuild[PacletObject["TuringMachineSearch"]]