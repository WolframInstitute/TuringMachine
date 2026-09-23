(* ::Package:: *)

(* CloudDeployNotebooks.wl

   Builds the computational footnotes of the blueprint and publishes them
   next to the site. Each Blueprint/Notebooks/<LeanName>.md (a
   MarkdownToNotebook computational essay using the paclet
   WolframInstitute/TuringMachine) is converted with its outputs evaluated,
   written to _out/notebooks/<LeanName>.nb, deployed as a public cloud
   notebook <base>/notebooks/<LeanName>.nb, and rasterized to a preview
   <base>/notebooks/<LeanName>.png that the blueprint shows before the live
   notebook loads. The paclet archive is deployed as
   <base>/WolframInstitute__TuringMachine.paclet, which the footnotes'
   first cell installs.

   Usage, from the Lake root (Proofs/), with a connected cloud account:

     wolframscript -file scripts/CloudDeployNotebooks.wl                    # build only
     wolframscript -file scripts/CloudDeployNotebooks.wl Smith.row          # build one footnote
     wolframscript -file scripts/CloudDeployNotebooks.wl deploy             # build and deploy

   The script part runs only when this file is the script itself, so Get of
   the file from another script only defines the functions. *)

BeginPackage["CloudDeployNotebooks`"];

BuildFootnote::usage = "BuildFootnote[md, outDir] converts a footnote to an evaluated notebook and returns its path.";
DeployFootnote::usage = "DeployFootnote[nb, base] deploys a built footnote and its preview under base/notebooks.";
DeployPaclet::usage = "DeployPaclet[pacletDir, base] builds the paclet archive and deploys it under base.";

Begin["`Private`"];

$mtn := $mtn = ResourceFunction[ResourceObject[
    "https://www.wolframcloud.com/obj/nikm/DeployedResources/Function/MarkdownToNotebook"]];

BuildFootnote[md_String, outDir_String] := Module[{out},
    Quiet @ CreateDirectory[outDir, CreateIntermediateDirectories -> True];
    out = FileNameJoin[{outDir, FileBaseName[md] <> ".nb"}];
    $mtn[md, out, "UseCache" -> False];
    out
];

(* The preview is the top of the notebook: the full rasterization at 96 dpi,
   or, for a notebook too tall for that, as many of its first cells as rasterize; cropped to 2400
   pixels. *)
preview[nb_String] := UsingFrontEnd @ Module[{obj, img},
    obj = NotebookOpen[nb, Visible -> False];
    SetOptions[obj, WindowSize -> {640, Automatic}];
    img = Quiet @ Rasterize[obj, ImageResolution -> 96];
    NotebookClose[obj];
    If[!ImageQ[img],
        Do[If[!ImageQ[img],
            obj = NotebookOpen[nb, Visible -> False];
            SetOptions[obj, WindowSize -> {640, Automatic}];
            With[{cells = Cells[obj]}, If[Length[cells] > k, NotebookDelete[cells[[k + 1 ;;]]]]];
            img = Quiet @ Rasterize[obj, ImageResolution -> 96];
            NotebookClose[obj, Interactive -> False]], {k, {14, 11, 9, 7, 5}}]];
    If[ImageQ[img], ImageTake[img, UpTo[2400]], img]
];

DeployFootnote[nb_String, base_String] := Module[{name = FileBaseName[nb], url, png},
    url = CloudDeploy[Import[nb, "NB"], CloudObject[base <> "/notebooks/" <> name <> ".nb"],
        Permissions -> "Public"];
    png = ExportByteArray[preview[nb], "PNG"];
    CloudDeploy[HTTPResponse[png, <|"ContentType" -> "image/png"|>],
        CloudObject[base <> "/notebooks/" <> name <> ".png"], Permissions -> "Public"];
    First[url]
];

DeployPaclet[pacletDir_String, base_String] := Module[{archive},
    archive = CreatePacletArchive[pacletDir, $TemporaryDirectory];
    CloudDeploy[HTTPResponse[ReadByteArray[archive], <|"ContentType" -> "application/octet-stream"|>],
        CloudObject[base <> "/WolframInstitute__TuringMachine.paclet"], Permissions -> "Public"];
    FileNameTake[archive]
];

End[];
EndPackage[];

If[$EvaluationEnvironment === "Script" && $ScriptCommandLine =!= {} &&
        FileBaseName[First[$ScriptCommandLine]] === "CloudDeployNotebooks",
    Module[{args = Rest[$ScriptCommandLine], local, only, root, pacletDir, mds, nbs},
        local = !MemberQ[args, "deploy"];
        only = DeleteCases[args, "deploy"];
        root = Directory[];
        pacletDir = FileNameJoin[{ParentDirectory[root], "TuringMachine"}];
        PacletDirectoryLoad[pacletDir];
        Needs["WolframInstitute`TuringMachine`"];
        mds = FileNames["*.md", FileNameJoin[{root, "Blueprint", "Notebooks"}]];
        If[only =!= {}, mds = Select[mds, MemberQ[only, FileBaseName[#]] &]];
        nbs = (Print["building ", FileBaseName[#]]; CloudDeployNotebooks`BuildFootnote[#, FileNameJoin[{root, "_out", "notebooks"}]]) & /@ mds;
        If[!local,
            If[!TrueQ[$CloudConnected], CloudConnect[]];
            Print["connected as ", $CloudUserID];
            If[!StringStartsQ[ToString[$CloudUserID], "wolframinstitute"],
                Print["refusing to deploy: not the wolframinstitute account"]; Exit[1]];
            Print["paclet ", CloudDeployNotebooks`DeployPaclet[pacletDir, "wolfram23-blueprint"]];
            Scan[Print["deployed ", CloudDeployNotebooks`DeployFootnote[#, "wolfram23-blueprint"]] &, nbs]
        ]
    ]
];
