# Blueprint of the Lean proof of Wolfram (2,3) universality

Status: narrative started 2026-09-21, plain Markdown; chapter 10 updated 2026-09-22
when T6 landed. The Verso port (verso-blueprint, see `docs/PUBLISHING.md`) is pending;
these files are written so that the port is a change of markup, not of content.

## What this is

A blueprint is the prose companion of a formal proof: one chapter per link of the
argument, each stating the mathematics in words, quoting the formal statements that
carry it, and saying plainly what is proved, what is assumed, and what is left out.
The reader who wants the theorem reads chapter 01; the reader who wants to audit one
link reads that chapter and opens the module it names.

The formal development follows Alex Smith's 2007 proof (`docs/TM23Proof.pdf`) that
Wolfram's 2-state 3-colour machine emulates every two-colour cyclic tag system, and
adds a Cocke-Minsky reduction from binary Turing machines to cyclic tag systems.
`docs/PLAN.md` is the engineering record (targets T1 to T8, milestone notes M0 to
M8 and M7); `docs/REVIEW.md` is the audit that preceded the rebuild plus status notes.

## Chapters and modules

| Chapter | Link of the chain | Modules |
|---|---|---|
| 01-overview | the headline theorems and the chain | `Smith/Universality.lean`, `Smith/Infinite.lean` |
| 02-machine-model | the machine, Wolfram's table, the lookahead type, the bridge | `TM/Defs.lean`, `BiTM/Basic.lean`, `BiTM/Wolfram23Valid.lean`, `Smith/Lookahead.lean`, `Smith/Wolfram23Bridge.lean` |
| 03-tm-to-cts | T7: binary TM -> 2-tag -> cyclic tag | `TagSystem/TagRounds.lean`, `TagSystem/CockeMinsky.lean`, `TagSystem/TMToCTS.lean`, `TagSystem/TagToCTS.lean` |
| 04-cts-to-system5 | T1: cyclic tag -> System 5 | `Smith/Doubling.lean`, `Smith/Represents.lean`, `Smith/System5Runs.lean`, `Smith/Conjecture5.lean`, `Smith/ConjectureFive.lean` |
| 05-system5-to-system4 | T2: System 5 -> System 4 | `BiTM/System5ToSystem4.lean`, `Smith/System4Runs.lean`, `Smith/Conjecture4.lean` |
| 06-system4-to-system3 | T3 first half: System 4 -> System 3 | `Smith/ParityBlocks.lean`, `Smith/System3Runs.lean`, `Smith/Conjecture3.lean` |
| 07-systems-3-2-1-0 | T3 second half and T5: relabelings, loop-freeness | `Smith/Systems123.lean`, `Smith/LoopFree.lean` |
| 08-conjecture0 | T4: Smith's Conjecture 0 in finite form | `Smith/Conjecture0.lean` |
| 09-universality | T8: the composition | `Smith/Universality.lean` |
| 10-infinite-form | T6: the infinite form | `Smith/Guards.lean`, `Smith/Infinite.lean`, `Tests/InfiniteVectors.lean` |
| 11-open-items | what is not proved, and the documentation debt | |

## Conventions

- Declarations are referenced as wiki links with their full Lean name, for example
  `[[Smith.wolfram23_universal]]` or `[[TagSystem.t7_finite]]`. The Verso port turns
  each into a `\lean` reference that resolves against the doc-gen4 pages and the
  dependency graph. A name inside backticks without brackets is a local variable or an
  informal name.
- "Formal statements" sections quote signatures verbatim from the source at the time
  of writing (commit `97319c1` plus the working tree of 2026-09-21; chapter 10 from
  commit `1bb1791` of 2026-09-22). If a signature drifts, the source wins and the
  chapter must be updated.
- "Target" marks a result that is planned or in progress and not yet proved. Nothing
  marked as proved uses `sorry`, and no `native_decide` is used outside `Tests/`.
- Page numbers refer to `docs/TM23Proof.pdf`.
- Plain ASCII in prose; Unicode only inside quoted Lean.

## Port plan

1. `cp -R <verso-blueprint>/project_template blueprint-verso`, one Verso file per
   chapter, wiki links to `\lean` references, the dependency graph from the `\uses`
   annotations that the "Depends on" lines of each chapter already list.
2. Toolchain: the project is on Lean `4.32.2` with Mathlib `v4.32.2`. verso-blueprint
   tracks recent Lean releases. Decision pending: pin a verso-blueprint tag that builds
   on 4.32.2, or bump Mathlib first. Until decided, the Markdown here is the source.
3. doc-gen4 behind `-Kenv=dev`, Pages workflow at `docs/`, blueprint at `/`.
4. Open question from `docs/PUBLISHING.md` section 2: split `Proofs/` into its own
   repository. The paths in these chapters are relative to the Lake root and survive a
   split.
