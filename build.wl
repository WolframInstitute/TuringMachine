#!/usr/bin/env wolframscript
<< ExtensionCargo`
<< ExtensionBuild`

name = "TuringMachineSearch"

PacletDirectoryLoad[name]
paclet = PacletObject[name]

CargoBuild[paclet]
pacletFile = BuildPacletArchive[paclet]

PacletDirectoryUnload[name]

PacletInstall[pacletFile, ForceVersionInstall -> True]

CopyFile[pacletFile, CloudObject[name <> ".paclet", Permissions -> "Public"], OverwriteTarget -> True]