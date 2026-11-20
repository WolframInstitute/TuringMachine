(* ::Package:: *)

(* What build_docs.wls, submit.wls and release.wls share: PacletPage, the paclet's directory, how
   its documentation is built, and the check every archive passes.

   PacletPage comes from its GitHub repository at the tag PACLETPAGE_REF names, by default the one
   below, fetched into build/tools and read from the Kernel file of that copy: a paclet directory
   loaded beside an installed PacletPage loses to the installed one when it is newer. A failed
   fetch is fatal. *)

$repositoryDirectory = ParentDirectory[DirectoryName[$InputFileName]];
$pacletDirectory = FileNameJoin[{$repositoryDirectory, "TuringMachine"}];
$toolsDirectory = FileNameJoin[{$repositoryDirectory, "build", "tools"}];

$pacletPageRef = Replace[Environment["PACLETPAGE_REF"], Except[_String?(StringLength[#] > 0 &)] -> "v0.3.85"];

(* PacletPage's archive of a tag, extracted afresh, and its one top directory; the network is
   enabled for this kernel alone, since $AllowInternet is a machine-wide setting other kernels
   switch off *)
fetchPacletPage[ref_String] := Module[{name, zip, target, response, tops},
    name = "PacletPage-" <> StringReplace[ref, Except[WordCharacter | "." | "-"] -> "_"];
    zip = FileNameJoin[{$toolsDirectory, name <> ".zip"}];
    target = FileNameJoin[{$toolsDirectory, name}];
    response = Block[{$AllowInternet = True},
        URLRead["https://github.com/WolframInstitute/PacletPage/archive/" <> ref <> ".zip"]];
    If[ ! MatchQ[response, _HTTPResponse] || response["StatusCode"] =!= 200,
        Print["FATAL: could not fetch PacletPage ", ref]; Exit[1]];
    Quiet @ CreateDirectory[$toolsDirectory, CreateIntermediateDirectories -> True];
    If[FileExistsQ[zip], DeleteFile[zip]];
    BinaryWrite[zip, response["BodyByteArray"]]; Close[zip];
    If[DirectoryQ[target], DeleteDirectory[target, DeleteContents -> True]];
    ExtractArchive[zip, target];
    tops = Select[FileNames["*", target], DirectoryQ];
    If[ Length[tops] =!= 1 || ! FileExistsQ[FileNameJoin[{First[tops], "Kernel", "PacletPage.wl"}]],
        Print["FATAL: the PacletPage archive of ", ref, " holds no PacletPage paclet."]; Exit[1]];
    First[tops]
];

Get[FileNameJoin[{fetchPacletPage[$pacletPageRef], "Kernel", "PacletPage.wl"}]];
If[ ! MemberQ[$Packages, "WolframInstitute`PacletPage`"], Print["FATAL: PacletPage did not load."]; Exit[1]];
Print["PacletPage ", $pacletPageRef];

(* The pages are the markdown under TuringMachine/docs and the definition is
   TuringMachine/ResourceDefinition.md, PacletPage's defaults. Pages convert in this kernel alone,
   the default for a machine other builds share; PACLETPAGE_PARALLEL gives a number of parallel
   kernels instead. *)
$documentationOptions = {
    "Parallel" -> Replace[Environment["PACLETPAGE_PARALLEL"], {
        n_String /; StringMatchQ[n, DigitCharacter ..] && FromDigits[n] > 0 :> FromDigits[n],
        _ -> False
    }]
};

(* The Rust backend ships prebuilt for every platform under Binaries/ (an Asset extension, which
   PacletPage's LibraryLink check does not cover), built by scripts/build_all_targets.sh; an
   archive missing a platform's library is refused. *)
$systemIDs = {"MacOSX-x86-64", "MacOSX-ARM64", "Linux-x86-64", "Linux-ARM64", "Windows-x86-64"};
$libraryFile = <|"MacOSX-x86-64" -> "libndtm_search.dylib", "MacOSX-ARM64" -> "libndtm_search.dylib",
    "Linux-x86-64" -> "libndtm_search.so", "Linux-ARM64" -> "libndtm_search.so",
    "Windows-x86-64" -> "libndtm_search.dll"|>;
$archiveCheck = Function[archive, With[{files = Import[archive, {"ZIP", "FileNames"}]},
    AllTrue[$systemIDs, Function[id, With[{dir = "Binaries/ndtm_search-" <> id <> "/"},
        AnyTrue[files, StringEndsQ[dir <> $libraryFile[id]]] && AnyTrue[files, StringEndsQ[dir <> "Functions.wl"]]]]]]];
