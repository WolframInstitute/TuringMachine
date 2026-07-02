(* ci_build.wl - Package the paclet for CI (no cloud upload).
   Binaries are built and installed into TuringMachine/LibraryResources/<SystemID>/
   by build_all_targets.sh beforehand; no ExtensionCargo / PacletExtensions. *)

publisher = "WolframInstitute"
name = "TuringMachine"

PacletDirectoryLoad[FileNameJoin[{Directory[], name}]]
paclet = PacletObject[publisher <> "/" <> name]

(* Create Paclet Archive *)
Print["Creating Paclet Archive..."]
pacletFile = CreatePacletArchive[paclet["Location"]]
Print["Paclet created: ", pacletFile]
Print["Size: ", FileSize[pacletFile]]

(* Export version for GitHub Actions *)
version = paclet["Version"]
Print["Exporting version: ", version]
Export["paclet_version.txt", version, "String"]
