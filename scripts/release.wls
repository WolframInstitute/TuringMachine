#!/usr/bin/env wolframscript
(* Releases WolframInstitute/TuringMachine with PacletPage's PublishPacletPage, in one kernel and
   so one cloud account: builds the documentation as build_docs.wls does, deploys the paclet
   resource to wolframinstitute/DeployedResources/Paclet/WolframInstitute/TuringMachine, publishes
   the documentation site wolframinstitute/TuringMachine around it with the authoring notebooks as
   its sources, and checks the site. submit.wls submits the paclet to the Paclet Repository.

       wolframscript -f ~/.claude/skills/wolfram-cloud-account/run-as.wls wolframinstitute scripts/release.wls
       (or --dry-run: the build and the resource, not deployed)

   The account is PACLETPAGE_ACCOUNT, by default the Wolfram Institute's. *)

$ProgressReporting = False

Get[FileNameJoin[{DirectoryName[$InputFileName], "pacletpage.wl"}]]

account = Replace[Environment["PACLETPAGE_ACCOUNT"], Except[_String?(StringLength[#] > 0 &)] -> "wolframinstitute@wolframinstitute.org"]
result = Block[{$AllowInternet = True},
    PublishPacletPage[$pacletDirectory, "TuringMachine",
        "Account" -> account,
        "DryRun" -> MemberQ[$ScriptCommandLine, "--dry-run"],
        "Monitor" -> True,
        "BuildOptions" -> $documentationOptions,
        "ResourceOptions" -> {"ArchiveCheck" -> $archiveCheck},
        "SiteOptions" -> {"FeedbackOptions" -> {"Domains" -> {"wolframinstitute.org", "wolfram.com"}}, "VersionLabel" -> True, "Footer" -> True}
    ]
]
If[ ! AssociationQ[result], Print["FATAL: nothing was published."]; Exit[1]]
Print["documentation: ", Length[result["Build"]["Notebooks"]], " pages, failed ", result["Build"]["Failed"]]
Print["resource: ", result["Resource"]["Resource"], If[TrueQ[result["Resource"]["Deployed"]], "", " (dry run)"]]
If[ AssociationQ[result["Site"]], Print["site: ", result["Site"]["Site"]]]
If[ AssociationQ[result["Check"]],
    Scan[Print["check failed: ", #["Check"], ": ", #["Detail"]] &, Select[Normal[result["Check"]["Checks"]], ! TrueQ[#["OK"]] &]];
    Print["check: ", If[TrueQ[result["Check"]["OK"]], "everything is reachable", "problems found"]];
    Exit[If[TrueQ[result["Check"]["OK"]], 0, 1]]
]
