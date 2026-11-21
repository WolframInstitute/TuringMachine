#!/usr/bin/env wolframscript
(* Submits WolframInstitute/TuringMachine to the Wolfram Paclet Repository with PacletPage's
   SubmitPacletResource: the definition notebook's own check, a fresh PacletBuild checked to hold
   every documentation page, all five platforms' Rust libraries and to load alone in a fresh kernel,
   then the submission under the version in TuringMachine/PacletInfo.wl, which has to be newer than
   the repository's. The publisher, WolframInstitute, is nikm@wolfram.com's, the account it submits
   as. Build the documentation first, with build_docs.wls.

       wolframscript -f ~/.claude/skills/wolfram-cloud-account/run-as.wls nikm scripts/submit.wls --dry-run
       wolframscript -f ~/.claude/skills/wolfram-cloud-account/run-as.wls nikm scripts/submit.wls

   --dry-run does everything but the submission. *)

$ProgressReporting = False

Get[FileNameJoin[{DirectoryName[$InputFileName], "pacletpage.wl"}]]

result = Block[{$AllowInternet = True},
    SubmitPacletResource[$pacletDirectory,
        "Account" -> "nikm@wolfram.com",
        "DryRun" -> MemberQ[$ScriptCommandLine, "--dry-run"],
        "ArchiveCheck" -> $archiveCheck
    ]
]
If[ ! AssociationQ[result], Print["FATAL: nothing was submitted."]; Exit[1]]
Print[result["Name"], " ", result["Version"], ": ", If[TrueQ[result["Submitted"]], "submitted", "not submitted (dry run)"]]
Print["archive: ", result["Archive"], ", ", result["Pages"], " documentation pages"]
If[ KeyExistsQ[result, "Result"], Print["result: ", result["Result"]]]
