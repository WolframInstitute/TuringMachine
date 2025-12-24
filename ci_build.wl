(* ci_build.wl *)

(* 1. Authentication *)
$CloudConnected = False;
If[Environment["WOLFRAM_CLOUD_USERNAME"] =!= $Failed && Environment["WOLFRAM_CLOUD_PASSWORD"] =!= $Failed,
    CloudConnect[Environment["WOLFRAM_CLOUD_USERNAME"], Environment["WOLFRAM_CLOUD_PASSWORD"]];
    $CloudConnected = True;
    Print["Connected to Wolfram Cloud."];
,
    Print["WOLFRAM_CLOUD_USERNAME or WOLFRAM_CLOUD_PASSWORD not set. Skipping CloudConnect."];
];

(* 2. Install Build Dependencies *)
PacletInstall["https://www.wolframcloud.com/obj/nikm/ExternalEvaluate.paclet", ForceVersionInstall -> True];
PacletInstall["https://www.wolframcloud.com/obj/nikm/PacletExtensions.paclet", ForceVersionInstall -> True];

PacletDirectoryLoad["/opt/turingmachinesearch/TuringMachineSearch"]; (* Adjust path if needed or rely on relative *)

(* 3. Load Extensions *)
Needs["PacletManager`"];
Needs["ExtensionCargo`"];
Needs["ExtensionBuild`"];

name = "TuringMachineSearch";
paclet = PacletObject[name];

(* 4. CargoBuild - collects binaries built by build_all_targets.sh (or builds them if needed) *)
Print["Running CargoBuild..."];
ExtensionCargo`CargoBuild[paclet];

(* 5. Create Paclet Archive *)
Print["Creating Paclet Archive..."];
pacletFile = CreatePacletArchive[name];
Print["Paclet created: ", pacletFile];
Print["Size: ", FileSize[pacletFile]];

(* 6. Upload *)
If[$CloudConnected,
    cloudObj = CloudObject[name <> ".paclet"];
    CopyFile[pacletFile, cloudObj, OverwriteTarget -> True];
    SetOptions[cloudObj, Permissions -> "Public"];
    Print["Paclet uploaded to: ", cloudObj];
    Print["URL: ", URL[cloudObj]];
];
