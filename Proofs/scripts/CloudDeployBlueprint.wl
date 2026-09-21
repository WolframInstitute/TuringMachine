(* ::Package:: *)

(* CloudDeployBlueprint.wl

   Publishes the rendered blueprint site (the output of `lake exe vbp build`,
   by default Proofs/_out/site/html-multi) to the Wolfram Cloud as a tree of
   public cloud objects under one base path, and returns the URL of the
   site's index page.

   Every file is deployed as an HTTPResponse with an explicit content type
   chosen from its extension: the cloud serves a plain file copy of a `.js`
   or `.mjs` file as text/plain, which browsers refuse to run as a module,
   while an HTTPResponse is served with the type it carries. Directory URLs
   (`.../chapter/`) resolve to that directory's index.html on the cloud, so
   the site's relative links work unchanged.

   Usage, from the Lake root (Proofs/), after `lake exe vbp build`:

     wolframscript -file scripts/CloudDeployBlueprint.wl
     wolframscript -file scripts/CloudDeployBlueprint.wl _out/site/html-multi wolfram23-blueprint

   or, in a session, Get the file and call
   CloudDeployBlueprint[siteDir, basePath]. Requires a connected cloud
   account (CloudConnect). *)

BeginPackage["CloudDeployBlueprint`"];

CloudDeployBlueprint::usage = "CloudDeployBlueprint[siteDir, basePath] deploys every file under siteDir to public cloud objects basePath/<relative path> and returns the URL of basePath/index.html.";

Begin["`Private`"];

contentType[file_String] := Replace[ToLowerCase[FileExtension[file]], {
  "html" -> "text/html; charset=utf-8",
  "htm" -> "text/html; charset=utf-8",
  "css" -> "text/css; charset=utf-8",
  "js" -> "text/javascript; charset=utf-8",
  "mjs" -> "text/javascript; charset=utf-8",
  "json" -> "application/json; charset=utf-8",
  "map" -> "application/json; charset=utf-8",
  "svg" -> "image/svg+xml",
  "png" -> "image/png",
  "jpg" -> "image/jpeg",
  "jpeg" -> "image/jpeg",
  "gif" -> "image/gif",
  "ico" -> "image/x-icon",
  "webp" -> "image/webp",
  "woff" -> "font/woff",
  "woff2" -> "font/woff2",
  "ttf" -> "font/ttf",
  "otf" -> "font/otf",
  "txt" -> "text/plain; charset=utf-8",
  "xml" -> "application/xml; charset=utf-8",
  "pdf" -> "application/pdf",
  "wasm" -> "application/wasm",
  _ -> "application/octet-stream"
}];

deployOne[siteDir_String, basePath_String, file_String] := Module[{rel, obj},
  rel = StringReplace[
    StringDrop[file, StringLength[siteDir]],
    {StartOfString ~~ ("/" | "\\") -> "", "\\" -> "/"}];
  obj = CloudObject[basePath <> "/" <> rel];
  CloudDeploy[
    HTTPResponse[ReadByteArray[file], <|"ContentType" -> contentType[file]|>],
    obj, Permissions -> "Public"];
  rel
];

CloudDeployBlueprint[siteDirIn_String, basePath_String] := Module[
  {siteDir = ExpandFileName[siteDirIn], files, done, failed},
  If[!DirectoryQ[siteDir], Return[Failure["NoSiteDir", <|"MessageTemplate" -> "no directory `1`", "MessageParameters" -> {siteDir}|>]]];
  If[!TrueQ[$CloudConnected], CloudConnect[]];
  files = FileNames["*", siteDir, Infinity];
  files = Select[files, !DirectoryQ[#] &];
  Print["deploying ", Length[files], " files under ", basePath];
  done = {}; failed = {};
  Do[
    With[{r = Quiet@Check[deployOne[siteDir, basePath, f], $Failed]},
      If[r === $Failed, AppendTo[failed, f], AppendTo[done, r]]],
    {f, files}];
  If[failed =!= {}, Print["failed: ", failed]];
  Print["deployed ", Length[done], " files"];
  First[CloudObject[basePath <> "/index.html"]]
];

End[];
EndPackage[];

(* Script entry: arguments are the site directory and the base path. *)
If[MemberQ[$CommandLine, "-file"] || MemberQ[$CommandLine, "-script"],
  Module[{args = Rest[$ScriptCommandLine], siteDir, basePath},
    siteDir = If[Length[args] >= 1, args[[1]], "_out/site/html-multi"];
    basePath = If[Length[args] >= 2, args[[2]], "wolfram23-blueprint"];
    Print[CloudDeployBlueprint`CloudDeployBlueprint[siteDir, basePath]]
  ]
];
