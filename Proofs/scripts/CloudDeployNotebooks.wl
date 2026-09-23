(* ::Package:: *)

(* CloudDeployNotebooks.wl

   Builds the computational footnotes of the blueprint and publishes them
   next to the site. Each Blueprint/Notebooks/<LeanName>.md (a
   MarkdownToNotebook computational essay using the paclet
   WolframInstitute/TuringMachine) is converted with its outputs evaluated,
   written to _out/notebooks/<LeanName>.nb, deployed as a public cloud
   notebook <base>/notebooks/<LeanName>.nb in its published form: without
   the toolbars of the essay template. The blueprint embeds it next to the
   node.

   Usage, from the Lake root (Proofs/), with a connected cloud account:

     wolframscript -file scripts/CloudDeployNotebooks.wl                    # build only
     wolframscript -file scripts/CloudDeployNotebooks.wl Smith.row          # build one footnote
     wolframscript -file scripts/CloudDeployNotebooks.wl deploy             # build and deploy

   The script part runs only when this file is the script itself, so Get of
   the file from another script only defines the functions. *)

BeginPackage["CloudDeployNotebooks`"];

BuildFootnote::usage = "BuildFootnote[md, outDir] converts a footnote to an evaluated notebook and returns its path.";
DeployFootnote::usage = "DeployFootnote[nb, base] deploys the published form of a built footnote under base/notebooks.";
BuiltFootnote::usage = "BuiltFootnote[nb] gives the published form of a built footnote, without the template's toolbars.";

Begin["`Private`"];

$mtn := $mtn = ResourceFunction[ResourceObject[
    "https://www.wolframcloud.com/obj/nikm/DeployedResources/Function/MarkdownToNotebook"]];

BuildFootnote[md_String, outDir_String] := Module[{out},
    Quiet @ CreateDirectory[outDir, CreateIntermediateDirectories -> True];
    out = FileNameJoin[{outDir, FileBaseName[md] <> ".nb"}];
    $mtn[md, out, "UseCache" -> False];
    out
];

(* The published form of a footnote: MarkdownToNotebook writes the authoring
   notebook of the computational essay template, whose stylesheet docks the
   template's toolbars and whose TaggingRules drive them; both go. *)
BuiltFootnote[nb_String] := Module[{expr = Import[nb, "NB"]},
    expr = DeleteCases[expr, (DockedCells -> _) | (TaggingRules -> _), Infinity];
    Append[expr, Editable -> False]
];

DeployFootnote[nb_String, base_String] := First @ CloudDeploy[BuiltFootnote[nb],
    CloudObject[base <> "/notebooks/" <> FileBaseName[nb] <> ".nb"], Permissions -> "Public"];

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
            Scan[Print["deployed ", CloudDeployNotebooks`DeployFootnote[#, "wolfram23-blueprint"]] &, nbs]
        ]
    ]
];
