(* ci_build.wl - Package the paclet for CI (no cloud upload).
   The Rust library packages are already in place: build_all_targets.sh runs
   `cargo wl build` for the host and each cross target, which compiles the
   cdylibs and writes them - together with their generated Functions.wl
   loaders - into TuringMachine/Binaries/ndtm_search-<SystemID>/, where the
   paclet's "Asset" extension picks them up. *)

publisher = "WolframInstitute"
name = "TuringMachine"

PacletDirectoryLoad[FileNameJoin[{Directory[], name}]]
paclet = PacletObject[publisher <> "/" <> name]

If[ ! FileExistsQ[FileNameJoin[{paclet["Location"], "Binaries", "ndtm_search-" <> $SystemID, "Functions.wl"}]],
    Print["FATAL: no ndtm_search library package for ", $SystemID, "; run build_all_targets.sh first."];
    Exit[1]
]

(* Create Paclet Archive *)
Print["Creating Paclet Archive..."]
pacletFile = CreatePacletArchive[paclet["Location"]]
Print["Paclet created: ", pacletFile]
Print["Size: ", FileSize[pacletFile]]

(* Export version for GitHub Actions *)
version = paclet["Version"]
Print["Exporting version: ", version]
Export["paclet_version.txt", version, "String"]
