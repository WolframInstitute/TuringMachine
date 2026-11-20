#!/usr/bin/env wolframscript
(* Builds the WolframInstitute/TuringMachine documentation with PacletPage's
   BuildPacletDocumentation: every page under TuringMachine/docs becomes an authoring notebook under
   TuringMachine/Documentation/English, and TuringMachine/ResourceDefinition.md becomes
   TuringMachine/ResourceDefinition.nb, the definition the resource is deployed and submitted from.
   The markdown is the source; the notebooks are generated and gitignored. A page converts again only
   when its source, the paclet's code or the converter changed.

       wolframscript -f scripts/build_docs.wls             (or --no-cache: every example afresh)

   release.wls builds the same way before it publishes. *)

$ProgressReporting = False

Get[FileNameJoin[{DirectoryName[$InputFileName], "pacletpage.wl"}]]

(* an example that reaches the network needs $AllowInternet, a machine-wide setting other kernels
   switch off *)
result = Block[{$AllowInternet = True},
    BuildPacletDocumentation[$pacletDirectory, Sequence @@ $documentationOptions,
        "UseCache" -> ! MemberQ[$ScriptCommandLine, "--no-cache"],
        "Monitor" -> True
    ]
]
If[ ! AssociationQ[result], Print["FATAL: the documentation did not build."]; Exit[1]]
Print[Length[result["Notebooks"]], " pages", If[StringQ[result["Definition"]], " and the definition notebook", ""],
    ": ", Length[result["Converted"]], " converted, ", Length[result["Cached"]], " from the cache"]
If[ result["Unevaluated"] =!= <||>, Print["unevaluated sections: ", result["Unevaluated"]]]
If[ result["Failed"] =!= {}, Print["FATAL: pages that did not convert: ", result["Failed"]]; Exit[1]]
