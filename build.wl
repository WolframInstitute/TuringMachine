#!/usr/bin/env wolframscript
<< ExtensionCargo`
<< ExtensionBuild`

name = "TuringMachineSearch"

PacletDirectoryLoad[name]
paclet = PacletObject[name]

CargoBuild[paclet]
pacletFile = CreatePacletArchive[name]

Echo[StringTemplate["Paclet `` has size ``"][pacletFile, FileSize[pacletFile]]]

PacletDirectoryUnload[name]

PacletInstall[pacletFile, ForceVersionInstall -> True]

CopyFile[pacletFile, CloudObject[name <> ".paclet", Permissions -> "Public"], OverwriteTarget -> True]