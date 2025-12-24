(* ci_build.wl - Build paclet for CI (no cloud upload) *)

(* Install Build Dependencies *)
PacletInstall["https://www.wolframcloud.com/obj/nikm/ExternalEvaluate.paclet"];
PacletInstall["https://www.wolframcloud.com/obj/nikm/PacletExtensions.paclet"];

PacletDirectoryLoad[FileNameJoin[{Directory[], "TuringMachineSearch"}]];

Needs["ExtensionCargo`"];

name = "TuringMachineSearch";
paclet = PacletObject[name];

(* CargoCollect - collects binaries built by build_all_targets.sh *)
Print["Running CargoCollect..."];
ExtensionCargo`CargoCollect[paclet];

(* Create Paclet Archive *)
Print["Creating Paclet Archive..."];
pacletFile = CreatePacletArchive[name];
Print["Paclet created: ", pacletFile];
Print["Size: ", FileSize[pacletFile]];
