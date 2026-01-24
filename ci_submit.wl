#!/usr/bin/env wolframscript
(* ci_submit.wl - Submit paclet to Wolfram Paclet Repository *)
(* Based on https://github.com/rhennigan/MCPServer/blob/main/Scripts/SubmitPaclet.wls *)

print[a___] := WriteString["stdout", a, "\n"];

print["=== Starting Paclet Submission ==="];

Off[General::shdw];
Off[PacletInstall::samevers];

(* Install specific PacletCICD version from release URL *)
print["Installing Wolfram/PacletCICD v0.36.2..."];
If[!PacletObjectQ @ PacletObject["Wolfram/PacletCICD"],
    PacletInstall["https://github.com/WolframResearch/PacletCICD/releases/download/v0.36.2/Wolfram__PacletCICD-0.36.2.paclet"]
];

Needs["Wolfram`PacletCICD`"];
print["PacletCICD loaded"];

(* Enable debug mode *)
Wolfram`PacletCICD`$Debug = True;

(* Disable DNC hints that might cause issues *)
print["Disabling problematic DNC hints..."];
Needs["DefinitionNotebookClient`" -> None];
DefinitionNotebookClient`$DisabledHints = <|"MessageTag" -> #, "Level" -> All, "ID" -> All|> & /@ {
    "CodeInspectionFileIssue/TopLevel",
    "HeroImageSquashed", 
    "InternalContextWarning"
};

(* Set up ResourceSystemBase *)
print["Setting up ResourceSystemBase..."];
Needs["ResourceSystemClient`" -> None];
$ResourceSystemBase = With[{rsBase = Environment["RESOURCE_SYSTEM_BASE"]},
    If[StringQ[rsBase], rsBase, $ResourceSystemBase]
];
print["ResourceSystemBase: ", $ResourceSystemBase];

(* Set PublisherID from paclet *)
$pacletDir = "./TuringMachine";
$PublisherID = PacletObject[File[$pacletDir]]["PublisherID"];
print["PublisherID: ", $PublisherID];

(* Definition notebook *)
$defNB = File["./TuringMachine/ResourceDefinition.nb"];
print["Definition Notebook: ", $defNB];

If[!FileExistsQ[First[$defNB]],
    print["::error::Definition notebook not found: ", $defNB];
    Exit[1]
];

(* Load paclet directory *)
print["Loading paclet directory..."];
PacletDirectoryLoad[$pacletDir];

(* Submit with ExitOnFail *)
print["Submitting paclet..."];
result = Check[
    Wolfram`PacletCICD`SubmitPaclet[$defNB, "ExitOnFail" -> False],
    $Failed,
    {Wolfram`PacletCICD`SubmitPaclet::errors, General::error}
];

print["Submit result: ", result];
print["Result FullForm: ", FullForm[result]];

(* Check if SubmitPaclet failed to evaluate *)
If[MatchQ[result, _Wolfram`PacletCICD`SubmitPaclet],
    print["::error::Wolfram`PacletCICD`SubmitPaclet not defined"];
    Exit[1]
];

If[FailureQ[result] || result === $Failed,
    print["::error::Submission failed"];
    If[MatchQ[result, _Failure],
        print["Failure type: ", result["Type"]];
        print["Failure message: ", result["Message"]];
        print["Failure info: ", result["Information"]];
    ];
    Exit[1],
    print["=== Submission successful! ==="]
];
