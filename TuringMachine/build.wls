#!/usr/bin/env wolframscript
(* Build the WolframInstitute/TuringMachine paclet documentation from the
   structured markdown in docs/, writing each notebook into the standard paclet
   layout under Documentation/English/. Also builds the Paclet Repository
   submission notebook (ResourceDefinition.nb) from ResourceDefinition.md.

   The markdown is the source of truth; the .nb outputs are generated and
   gitignored. Re-author in the .md and re-run this script - never hand-edit
   the generated notebooks.

       wolframscript -f build.wls           # build all notebooks
       wolframscript -f build.wls --check   # build, then lint ResourceDefinition.nb

   Author the docs/ pages with the wolfram-symbol-page / wolfram-guide-page /
   wolfram-tech-note skills; the metadata in ResourceDefinition.md must agree
   with PacletInfo.wl. *)

print[args___] := WriteString["stdout", StringJoin[ToString /@ {args}], "\n"]

pacletDir = DirectoryName[$InputFileName]
check     = MemberQ[Rest[$ScriptCommandLine], "--check"]

(* Load MarkdownToNotebook from its public cloud deployment (it is not on the
   public Function Repository yet). *)
print["loading MarkdownToNotebook from Wolfram Cloud"]
mtn = ResourceFunction[ResourceObject[
    "https://www.wolframcloud.com/obj/nikm/DeployedResources/Function/MarkdownToNotebook"]]

(* Load the paclet so example and hero-image cells resolve its symbols during
   evaluation (the Rust backend is loaded from Binaries/). *)
PacletDirectoryLoad[pacletDir]
Needs["WolframInstitute`TuringMachine`"]

(* Documentation page layout, keyed by the markdown's frontmatter Template. *)
subdir["Symbol"]   = {"Documentation", "English", "ReferencePages", "Symbols"}
subdir["Guide"]    = {"Documentation", "English", "Guides"}
(* Overview shares the tutorial/ URI namespace with TechNotes, so they coexist
   in Documentation/English/Tutorials/. *)
subdir["TechNote"] = {"Documentation", "English", "Tutorials"}
subdir["Overview"] = {"Documentation", "English", "Tutorials"}

(* The output basename is the SOURCE basename - it must match the last segment
   of the doc URI (DocumentationBuild derives the URI from the file path). *)
buildDoc[srcFile_String] := Block[{info, tmpl, baseName, dir, out},
    info     = mtn[srcFile, "Association"];
    tmpl     = info["Template"];
    baseName = FileBaseName[srcFile];
    dir      = FileNameJoin[Prepend[subdir[tmpl], pacletDir]];
    Quiet @ CreateDirectory[dir, CreateIntermediateDirectories -> True];
    out = FileNameJoin[{dir, baseName <> ".nb"}];
    mtn[srcFile, out];
    print["  ", FileNameTake[srcFile], " -> ", FileNameJoin[Append[subdir[tmpl], baseName <> ".nb"]]]
]

print["building TuringMachine documentation"]
docs = Sort @ FileNames["*.md", FileNameJoin[{pacletDir, "docs"}], Infinity];
If[docs === {}, print["  (no docs/*.md pages yet)"], Scan[buildDoc, docs]]

(* Paclet Repository submission notebook at the paclet root. *)
rd  = FileNameJoin[{pacletDir, "ResourceDefinition.md"}]
rdo = FileNameJoin[{pacletDir, "ResourceDefinition.nb"}]
If[FileExistsQ[rd],
    mtn[rd, rdo];
    print["  ResourceDefinition.md -> ResourceDefinition.nb"]
]

(* Optional: lint the submission notebook against the Paclet Repository
   guidelines. The headless build does not assign CellIDs, and the linter
   needs them to locate cells, so stamp + save through the front end first
   (see the wolfram-paclet skill). *)
If[check && FileExistsQ[rdo],
    print["checking ResourceDefinition.nb"];
    Needs["DefinitionNotebookClient`"];
    UsingFrontEnd @ Block[{nbo = NotebookOpen[File[rdo]]},
        CurrentValue[nbo, CreateCellID] = True;
        SelectionMove[nbo, All, Notebook];
        FrontEndTokenExecute[nbo, "Save"];
        Scan[print["  [", #["Level"], "] ", #["Tag"], " ", #["Parameters"]] &,
            Normal @ DefinitionNotebookClient`CheckDefinitionNotebook[nbo]];
        NotebookClose[nbo]
    ]
]

print["done"]
