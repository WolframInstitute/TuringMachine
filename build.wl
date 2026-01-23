#!/usr/bin/env wolframscript

PacletInstall["https://www.wolframcloud.com/obj/nikm/ExternalEvaluate.paclet"]
PacletInstall["https://www.wolframcloud.com/obj/nikm/PacletExtensions.paclet"]

<< ExtensionCargo`

publisher = "WolframInstitute"
name = "TuringMachine"

PacletDirectoryLoad[name]
paclet = PacletObject[publisher <> "/" <> name]

CargoCollect[ParentDirectory[paclet["Location"]], FileNameJoin[name, "Binaries"]]
pacletFile = CreatePacletArchive[name]

Echo[StringTemplate["Paclet `` has size ``"][pacletFile, FileSize[pacletFile]]]

PacletDirectoryUnload[name]

PacletInstall[pacletFile, ForceVersionInstall -> True]

CopyFile[pacletFile, Echo @ CloudObject[name <> ".paclet", Permissions -> "Public"], OverwriteTarget -> True]