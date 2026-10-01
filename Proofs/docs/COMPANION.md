# Plan: computational companion notebooks for the Lean proof

Date: 2026-09-23. Status: the WL functions of section 3.1 (milestone N1) are built:
`TuringMachine/Kernel/Emulation.wl`, 19 reference pages, the tech note
`SmithsUniversalityProof`, and `TuringMachine/Tests/Emulation.wlt` against vectors that
`scripts/ExportVectors.lean` writes from the Lean definitions. The notebook panel (N0,
N2-N5) is not built.

## 1. Goal

Every definition and theorem of the Smith chain that a reader might want to *see*
gets a short Wolfram notebook: a computation footnote with runnable examples and
pictures. For a definition that means the object built and drawn. For a theorem it
means the statement checked on instances, with the bound or schedule plotted against
the actual run. The notebooks are generated with the `WolframInstitute/TuringMachine`
paclet. The paclet gets a Wolfram Language (WL) version of each Lean definition, in its
main context, with one function per arrow of the chain.

The blueprint shows the footnote of the node being read in a panel to the right of
the text. The paclet's documentation shows the same material as tech notes, with
links back to the blueprint and to the Lean source.

The notebooks are illustrations. They are not part of the trusted base; the Lean
kernel is. Section 5 keeps the WL versions and the Lean definitions in step, so a
picture never shows something the Lean definition does not do.

## 2. What exists

- **Paclet** (`TuringMachine/`): the kernel files `Functions`, `Multiway`,
  `Visualizations`, `Compiled` (Rust) and the `InductiveProofs` subcontext. The
  documentation has reference pages, a guide and two tutorials. Nothing about tag
  systems, Systems 5 to 0, or Smith's encoders.
- **Blueprint** (`Proofs/Blueprint/`): Verso Blueprint, 282 nodes whose labels are
  full Lean names. It is published on GitHub Pages and on the Wolfram Cloud
  (`scripts/CloudDeployBlueprint.wl`).
- **Hooks Verso already has**:
  - `block_extension` with `toHtml`, `extraCss` and `extraJs` (VersoBlueprint's
    `RustBlock` uses these to attach a panel to a node);
  - margin notes (`VersoManual.Marginalia`, with a layout that already reacts to the
    content width);
  - a manifest `-verso-data/blueprint-manifest.json` keyed by label.
- **Embedding**: `wolfram-notebook-embedder` (0.3.0) is on cdn.jsdelivr.net, which the
  site may load. It embeds a public cloud notebook as live, interactive content.

## 3. Architecture

### 3.1 The WL version of the chain

Everything goes in the main ``WolframInstitute`TuringMachine` `` context: no
subcontext. There is one function per arrow, named after the systems it connects,
together with the matching decoder and stepper. Usage messages name the Lean
counterpart.

| Arrow | Lean | WL function (proposed) | Decoder |
| --- | --- | --- | --- |
| TM -> 2-tag | `TagSystem.tagK`, `word`, `tagTime` | `TuringMachineToTagSystem[machine, config, n]` | `TagSystemToTuringMachine` (`decodeWord`) |
| 2-tag -> cyclic tag | `tagToCTS`, `tagConfigToCTS` | `TagSystemToCyclicTagSystem[tag]` | `CyclicTagSystemToTagSystem` (`tagWordDecode`) |
| cyclic tag -> System 5 | `ctsToSystem5` (budget `N` cycles) | `CyclicTagSystemToSystem5[cts, N]` | `System5ToCyclicTagSystem` (`decodeBag`) |
| System 5 -> System 4 | `system5ToSystem4 s f` | `System5ToSystem4[s5, f]` | `System4ToSystem5` (`decodeS4`, band `b`) |
| System 4 -> System 3 | `initAC w h`, `AC.toL` | `System4ToSystem3[s4, w, h]` | |
| System 3 -> wolfram23 | `phi3`, `phi2`, `toBi` | `System3ToWolfram23[s3]` | `Wolfram23ToSystem5` (`decodeBlocks`) |
| parameters | `icB` ... `icW` | `EmulationParameters[s5, "Exact" \| "ClosedForm"]`, `EmulationSizes[machine, config, n]` | |

Each system has an evolution function (`TagSystemEvolution`, ..., `Wolfram23Evolution`)
whose form `[x, n, crit]` keeps only the configurations that satisfy `crit`. No composite
initial-condition function was built: the composite is never materializable (see below).

Every Lean encoder is a computable definition: none is `noncomputable`, and only the
choice of the parameters `N`, `f`, `w`, `h` depends on runs. The functions are
therefore all constructible. Materializing their output is another matter. Sizes for
`tmH` (2 states, halts after one step) from `1, [], 0, []`, emulating that one step
(`N = tagTime 1 = 6` cycles), with the smallest parameters the proof allows (the
exact run lengths):

| Stage | Size | Growth |
| --- | --- | --- |
| tag word | 4 symbols, 338 productions | exponential in the tape size (Cocke-Minsky writes `val left` in unary) |
| cyclic tag | 676 bits, 338 appendants (63544 bits) | x `1 + 84 S` bits per symbol |
| System 5 | 8112 rules, 1.5M integers (max 1532282); runs 2242200 steps | linear in `N`; the run length is what drives everything after |
| System 4 | `1 + 2f + 8fR` elements with `f = 18050053`: 1.2e12 | `f > 2 x` (System 5 run length) |
| System 3 / wolfram23 | (number of sets) x `2^w` cells, `2^w >=` System 4 fuel: 1e24 to 1e36 cells | relabeling is free |

So the chain is fully materializable up to System 5 for real machines. System 4 and
beyond can be built outright only for small programs (Smith's D1-D10 and the
E-blocks). For real machines those stages need a lazy representation: a
cell-at-index function computed from the block structure (sets are parity-row XORs
with closed forms, and the rest is arithmetic on the block lengths). The same
accessor serves `ITape tm c`, which is infinite anyway. The closed-form parameters of
`IC` are far larger still (`icF` of the one-cycle `tmH` program has about 400 digits),
so `"ClosedForm"` mode can only report parameters and answer cell queries.

Side finding, done 2026-09-23: the proof picked `w = fuel + 3f + 6`, but it only needs
`2^w >= fuel + 3` and `2^w >= 3f + 3`. `icW` and `blkW` are now the bit length
`Nat.size (fuel + 3f + 6)`, so the System 3 tape of `IC` is linear in the System 4 data
instead of exponential.

### 3.2 Footnote notebooks

- **Authoring**: one tech note per blueprint chapter (11 notebooks) in
  `TuringMachine/Documentation/English/Tutorials/Smith/`. Each footnote is a cell
  group whose cell tag is the Lean name (for example `Smith.System4.run_bound`).
  Authors work in one notebook per chapter. The paclet's documentation shows it as
  an ordinary tech note.
- **Extraction** (`scripts/CompanionBuild.wl`): split every tagged cell group into
  its own small notebook. Add a header with the Lean name, the statement in one line
  and links to the blueprint node and the GitHub source. Evaluate it, deploy it
  publicly to `wolfram23-blueprint/notebooks/<LeanName>.nb`, and export a static
  preview (PNG, plus a text summary for search).
- **Registry**: the build script writes `Proofs/Blueprint/companion.json`, mapping
  each Lean name to its cloud URL, preview path, WL symbols and chapter. This file is
  the only link between the two worlds.

### 3.3 The blueprint side panel

- **The notebook directive**: `:::notebook "Smith.System4.run_bound"` is a
  `block_extension` placed after a node. At elaboration it reads `companion.json` and
  fails the build if the name is not in the registry or is not a declaration. Its
  HTML is a marker `<div data-nb=... data-preview=...>` plus a "notebook" chip in the
  node header.
- **Wide layout** (content width about 1100px or more): a sticky right column, in
  the space the margin notes use. A script loaded with `extraJs` uses an
  `IntersectionObserver` to follow the node nearest the reading position and shows
  that node's footnote.
  - It shows the static preview first and loads the live embed on click, or after
    the node has been in view for a moment. At most one live notebook is loaded at a
    time, since cloud notebooks are heavy.
  - A pin button keeps the current notebook while you scroll. There is also an
    "open in Wolfram Cloud" link and a "download .nb" link.
- **Narrow layout**: the chip opens a bottom drawer with the same content. No
  horizontal scroll.
- **Theming and fallbacks**: the panel follows the site's dark mode for its frame;
  notebooks render in their own style. Print and TeX output show the static preview
  and the URL.
- **GitHub Pages**: it cannot run Wolfram Language in CI (no license), so the Pages
  site embeds the cloud URLs cross-origin. The previews are committed, or fetched
  from the cloud at deploy time (decision D3).

### 3.4 The paclet documentation

- Each tech note links every footnote heading to its blueprint node, using a
  `ButtonData` URL built from the chapter tag and the label.
- Reference pages for the new public symbols give the Lean counterpart in their
  details section.
- The guide page gets a "Smith's proof (Lean companion)" section.

## 4. Milestones

| Id | Deliverable | Acceptance check |
| --- | --- | --- |
| N0 | Spike, one node end to end: `System4Step`, `System5ToSystem4`, a tape plot, the footnote for `Smith.System4.run_bound` (runs vs bound on D4), extraction, cloud deploy, the `:::notebook` directive and the right panel on the Conjecture 0 chapter | the live embed and the preview work on both sites; the narrow-screen drawer works; the build fails on a misspelt name |
| N1 | The arrow functions, decoders and steppers (section 3.1; lazy cell access for System 4 and beyond) and differential tests (section 5) | all vectors of `Vectors/` reproduced in WL; the test report passes |
| N2 | `CompanionBuild.wl` for all chapters, `companion.json`, directive check, deploy folded into `CloudDeployBlueprint` | one command rebuilds and redeploys the notebooks and the site |
| N3 | Tech notes, chapter by chapter, starting with the heaviest reading: System 5 to 4, System 4 to 3 (parity blocks), infinite form (guards, block chain), closed form (bounds, parameters), then the rest | every node in the "headline", "t4_run_bounds", "guards" and "chain" groups has a footnote; the other nodes where a picture helps |
| N4 | Panel polish: scroll sync, pinning, dark mode, print, keyboard access, lazy-loading budget | Lighthouse accessibility at least 90; no more than one live embed loaded at a time |
| N5 | Paclet release: reference pages, guide section, tech notes in the documentation build, version bump | `PacletDocumentationBuild` clean; the tech notes open from the Documentation Center |

N0 is the go/no-go point. If the embed is too slow or not reliable enough, the panel
stays static-first (previews plus an "open in cloud" link), and the rest of the plan
is unchanged.

## 5. Keeping WL and Lean in step

- **Lean exports runs.** A small Lean executable, `lake exe companion-vectors`, uses
  `#eval`-able code already in the tree to write JSON for each vector: System 5 and 4
  runs of D1 to D10, tag times of `tmH` and `tmEx`, the E-block runs, and the
  closed-form parameters of D4.
- **WL compares.** `TuringMachine/Tests/Smith.wlt` runs the WL functions on the same
  inputs and compares them exactly. A mismatch fails the paclet tests.
- **WL proposes vectors.** New interesting instances found in WL (for example a
  program whose System 4 run gets closest to its bound) are added as `decide` vectors
  in `Vectors/`. The two directions check each other.
- **Every footnote states its source.** Each footnote names the Lean declaration and
  the commit it was checked against. The build script refuses a Lean name the
  registry does not know.

## 6. Decisions to make

- **D1, live embed or static first.** Recommended: static preview first, live on
  click. It is fast, works without a cloud session, and prints.
- **D2, how footnotes are authored.** Recommended: in chapter tech notes, extracted by
  cell tag. Authoring one notebook per declaration directly means about 150 files to
  maintain.
- **D3, where previews live.** Recommended: deploy them to the cloud next to the
  notebooks and fetch them at Pages deploy time. Committing them into the repo means
  binary churn in git.
- **D4, public or internal WL functions.** Recommended: public, with reference pages,
  so the tech notes use documented functions. They live in the main context. The cost
  is API surface to keep stable.
- **D5, cloud account.** `wolframinstitute` for everything public. The deploy script
  should check `$CloudUserID` and refuse any other account (the M9 deploy went to
  `nikm` by mistake).

## 7. Risks

- **Embed weight**: a cloud notebook embed is several MB of JavaScript plus a kernel
  session. Mitigated by static-first loading and one embed at a time.
- **Cross-origin embedding** from github.io may run into cookie or third-party
  limits for interactive (Manipulate) content. The N0 spike tests this; the fallback
  is the static preview plus a link.
- **Drift** between WL and Lean after a refactor. Mitigated by the differential tests
  of section 5 and the registry check.
- **Verso Blueprint upgrades** may change the node HTML the panel script hooks into.
  Keep the script keyed to the `data-nb` markers the directive emits, not to
  VersoBlueprint's classes.
