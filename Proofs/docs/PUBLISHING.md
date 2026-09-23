# Publishing the Lean proof as an interactive site

Date: 2026-09-21 (proposal); decisions and setup 2026-09-22. Companion to PLAN.md and
REVIEW.md.

## 1. Decisions (2026-09-22)

- In-tree: the Lake root stays `Proofs/` inside the paclet repository; no split. The
  open questions of the proposal (section 6) are closed by this and the next two items.
- Toolchain: Lean `v4.34.0` with Mathlib `v4.34.0`, the release line verso-blueprint
  publishes for (its `v4.34.0` branch; its own Verso pin is built on `v4.34.0-rc2`).
  Bumped from `v4.32.2` on 2026-09-22.
- Two hosts: GitHub Pages at <https://wolframinstitute.github.io/TuringMachine/> (the
  repository is `WolframInstitute/TuringMachine`, public; the Pages source is "GitHub
  Actions", enabled through `gh api repos/WolframInstitute/TuringMachine/pages -f
  build_type=workflow`), and the Wolfram Cloud under the `wolframinstitute` account.
- The blueprint covers the Smith chain and the machine reduction (M0 to M8, M7), not
  the `OneSidedTM` class proofs that share the `lean_lib`.

## 2. Layout

| Piece | Where |
|---|---|
| Verso chapters | `Proofs/Blueprint/Chapters/*.lean`, one module per link of the chain (Overview, MachineModel, TMToCTS, CTSToSystem5, System5ToSystem4, System4ToSystem3, Systems3210, Conjecture0, Universality, InfiniteForm, OpenItems) |
| Top-level document | `Proofs/Blueprint.lean` (includes, dependency graph, progress summary) |
| Generator entry point | `Proofs/BlueprintMain.lean` (`vbp` discovers it by name) |
| Lake | `require VersoBlueprint ... @ "v4.34.0"` and `lean_lib Blueprint` in `Proofs/lakefile.lean` |
| Site output | `Proofs/_out/site/html-multi/` (ignored by git) |
| Pages workflow | `.github/workflows/blueprint-pages.yml` at the repository root, `working-directory: Proofs` |
| Wolfram Cloud deploy | `Proofs/scripts/CloudDeployBlueprint.wl` |
| Codespaces | `Proofs/.devcontainer/devcontainer.json` (to move to the repository root if a Codespaces badge is wanted; Codespaces reads `.devcontainer` at the root) |

Chapters import the proof modules and link each statement to its declaration with
`(lean := "Full.Name")`, so the site renders the real signatures and their Lean
status; blueprint labels are the full Lean names. Mentions of declarations in prose
are `{bpref}` links to their nodes; mentions of source files are links to the file on
GitHub (`https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/...`;
change `lean-proofs` to `main` in the chapters when the branch is merged), and mentions
of Smith's paper link to its public copy at
<https://www.wolframscience.com/prizes/tm23/TM23Proof.pdf>. Chapter cross references use
`{ref "tag"}[text]` with the tags `overview`, `machine-model`, `tm-to-cts`,
`cts-to-system5`, `system5-to-system4`, `system4-to-system3`, `systems-3-2-1-0`,
`conjecture0`, `universality`, `infinite-form`, `open-items`. The Markdown chapters that
preceded the port (2026-09-21) were the source of the Verso modules and were removed
with the port (git history has them under `docs/blueprint-md/` and `blueprint/`).

## 3. Building and publishing

Local:

```
cd Proofs
lake exe cache get          # the Mathlib cache
lake build                  # the proofs, the tests and the Blueprint library
lake exe vbp build          # the site, to _out/site/html-multi
lake exe vbp build --serve  # local preview
```

GitHub Pages: every push to `main` or `lean-proofs` that touches `Proofs/` runs the
workflow (build, `sorry`/`native_decide` scan, axiom check of both headline theorems,
`vbp build`, upload, deploy); `workflow_dispatch` runs it by hand. The first run
compiles Verso from source (the Lake packages are cached between runs).

Computational footnotes: each `:::notebook "Lean.Name"` directive in a chapter
(defined in `Blueprint/Notebook.lean`) needs `Blueprint/Notebooks/<Lean.Name>.md`, a
MarkdownToNotebook computational essay using the paclet functions; the build fails
without it. The pages show a button that opens a panel on the right with the footnote's
preview and, on request, the live notebook (`wolfram-notebook-embedder` from jsdelivr).
The notebooks, their previews and the paclet archive the notebooks install are
deployed under `wolfram23-blueprint/` on the cloud, for both sites:

```
wolframscript -file scripts/CloudDeployNotebooks.wl                 # build into _out/notebooks
wolframscript -file scripts/CloudDeployNotebooks.wl Smith.row       # build one footnote
wolframscript -file scripts/CloudDeployNotebooks.wl deploy          # build and deploy
```

The build does not use MarkdownToNotebook's output cache (`"UseCache" -> False`): the
cache is keyed by the notebook title, and an entry written while the paclet was not
loaded would otherwise be served again. `wolframscript` takes `-`-prefixed words as
its own options, so the script's arguments are plain words.

Wolfram Cloud: after `lake exe vbp build`,

```
wolframscript -file scripts/CloudDeployBlueprint.wl _out/site/html-multi wolfram23-blueprint
```

deploys every file as a public cloud object under `wolfram23-blueprint/` with an
explicit content type and prints the index URL. Facts established by experiment on
2026-09-22 with the `wolframinstitute` account: directory URLs resolve to `index.html`
on the cloud, so the site's relative links work unchanged; binary files round-trip;
a plain file copy (`CopyFile`) of a `.js` or `.mjs` file is served as `text/plain`,
which browsers refuse to execute as a module, while an `HTTPResponse` object is served
with the content type it carries, which is why the script deploys every file that way.

## 4. Background: the three layers (from the proposal)

| Layer | Tool | What the reader gets | Hosting |
|---|---|---|---|
| Structure | [verso-blueprint](https://github.com/leanprover/verso-blueprint) | Prose and Lean cross-links, the dependency graph, hover previews, the progress summary, PDF from the same source | GitHub Pages, Wolfram Cloud |
| Declarations | doc-gen4 | a page per declaration from the docstrings | not done |
| Goal states | `.devcontainer` and an "Open in Codespaces" badge | VS Code with the infoview and the Mathlib cache; step through any tactic | none |

verso-blueprint is the official successor of Patrick Massot's plasTeX `leanblueprint`.
Not recommended for now: self-hosting lean4web or the Lean Workbench (both need a
server with Lean and Mathlib resident in RAM); Codespaces gives the same experience.

## 5. Not done

- doc-gen4 pages per declaration: the blueprint's `(lean := ...)` links render the
  signatures from the environment, which covers the main need; doc-gen4 would add the
  docstrings and the source links. `require «doc-gen4»` behind `-Kenv=dev`,
  `lake -R -Kenv=dev build OneSidedTM:docs`, publish `.lake/build/doc` under `/docs/`.
- The PDF build (`lake exe vbp build --pdf`, needs lualatex and the TeX Live packages
  listed in the verso-blueprint manual).
- The Codespaces badge (needs `.devcontainer` at the repository root).

## 6. Questions closed on 2026-09-22

- Split repo or in-tree: in-tree.
- Bump to the toolchain verso-blueprint supports, or pin verso-blueprint to 4.32.2: bump.
- Blueprint scope: the chain only.
