#!/usr/bin/env wolframscript

PacletInstall["https://www.wolframcloud.com/obj/nikm/ExternalEvaluate.paclet"]
PacletInstall["https://www.wolframcloud.com/obj/nikm/PacletExtensions.paclet"]

<< ExtensionCargo`

name = "TuringMachineSearch"

PacletDirectoryLoad[name]
paclet = PacletObject[name]

CargoCollect[paclet]
pacletFile = CreatePacletArchive[name]

Echo[StringTemplate["Paclet `` has size ``"][pacletFile, FileSize[pacletFile]]]

PacletDirectoryUnload[name]

PacletInstall[pacletFile, ForceVersionInstall -> True]

CopyFile[pacletFile, Echo @ CloudObject[name <> ".paclet", Permissions -> "Public"], OverwriteTarget -> True]