# Proposal: publishing the Lean proof as an interactive site

Date: 2026-09-21. Companion to PLAN.md and REVIEW.md. Status: narrative started 2026-09-21
in `blueprint/` (Markdown, Verso port pending); scaffolding for steps 1 and 3 written.

Created on 2026-09-21:

- `blueprint/README.md` and chapters `01-overview` to `11-open-items`, one per link of the
  chain plus the T6 specification (chapter 10) and the open items from the review
  (chapter 11). Declarations are wiki-linked by full Lean name for the Verso port; key
  statements are quoted verbatim from the source.
- `README.md` (project in one screen, axiom check, build, where things are, Codespaces
  placeholder), `.devcontainer/devcontainer.json`, `.github/workflows/ci.yml` (inert until
  the repository split: GitHub reads workflows from the repository root; move it up and keep
  `working-directory: Proofs` to run it in-tree).

Updated 2026-09-22 (T6 landed): chapter 10 of the blueprint rewritten from target to
proved, README and overview updated, the module headers named by the review corrected.

Remaining: doc-gen4 (step 2); the Verso port and the pin-or-bump decision (step 4); the
Pages workflow (step 5); the repo-split decision (section 2).

## 1. Recommendation

Three layers, each answering a different "can I click on it?":

| Layer | Tool | What the reader gets | Hosting |
|---|---|---|---|
| Structure | [verso-blueprint](https://github.com/leanprover/verso-blueprint) | Prose <-> Lean cross-links, clickable dependency graph (TM -> 2-tag -> CTS -> System 5 -> 4 -> 3 -> 2 -> 1 -> 0 -> `wolfram23_universal`), hover previews, progress summary, PDF from the same source | GitHub Pages |
| Declarations | doc-gen4 | mathlib-docs-style page per declaration, from the existing docstrings; blueprint links into it | GitHub Pages |
| Goal states | `.devcontainer` + "Open in Codespaces" badge | Real VS Code + infoview with the Mathlib cache fetched; step through any tactic | none |

verso-blueprint is the official successor of Patrick Massot's plasTeX `leanblueprint`
(FLT has migrated; the FRO roadmap for 2026-09 to 2027-02 lists it as a hardening target).
Do not start a plasTeX blueprint now.

Not recommended for now: self-hosting lean4web or the FRO's Lean Workbench (experimental,
self-host only). Both need a server with Lean + Mathlib resident in RAM. Codespaces gives the
same experience for free; revisit if a public Workbench instance appears.

## 2. Repo layout decision

The Lake root is `Proofs/` inside the Wolfram paclet repo. Blueprint, doc-gen4 and Pages
workflows assume the Lake project is the repo. Two options:

- (a) Split `Proofs/` into its own repo (`sw1sh/Wolfram23Lean` or similar), keep the paclet
  repo pointing at it. Cleaner for readers; drops `old_call_graphs/`, `sieve*.lean`,
  `trace.lean`, `group_rules.lean`, `lean_dep_*` and `Archive/` from what they see.
- (b) Stay in-tree, run every workflow with `working-directory: Proofs`, and exclude the
  clutter from the `lean_lib` roots (already the case) and from doc-gen4.

Preference: (a). The proof is a self-contained artefact with a different audience from the
paclet.

## 3. Steps

1. Prerequisites in the tree.
   - Docstring `wolfram23_universal` and the other three public statements in
     `Smith/Universality.lean` (3 docstrings today): the encoding, the `times`/`T` clock,
     the decoder, the size invariant.
   - Put `#print axioms wolfram23_universal` in the README (expected: `propext`,
     `Classical.choice`, `Quot.sound`). `Tests/` vectors and the "no sorry" grep go into CI.
2. doc-gen4. Add as a dev dependency in `lakefile.lean` (`require «doc-gen4» ... ` behind
   `Kenv=dev`), build with `lake -R -Kenv=dev build OneSidedTM:docs`, publish `.lake/build/doc`
   to Pages. Half a day.
3. Codespaces. `.devcontainer/devcontainer.json` on the Mathlib image, post-create
   `lake exe cache get && lake build`. Badge in the README. One hour.
4. verso-blueprint. `cp -R project_template blueprint`, `lake exe vbp build --serve`.
   One chapter per link of the chain, seeded from PLAN.md section 3 ("Proof architecture,
   link by link") and the M-notes in section 5; each theorem block carries `\lean`-style
   references to the declaration. Toolchain caveat: verso-blueprint tracks recent Lean
   (4.35.0-rc1 bump in flight); either pin a verso-blueprint tag for 4.32.2 or bump Mathlib
   first. Two to four days of writing; the prose is mostly already in PLAN.md.
5. Pages workflow that builds doc-gen4 and the blueprint on push to `main`, with the Mathlib
   cache. Blueprint site at `/`, docs at `/docs/`.

## 4. Open questions

- Split repo or in-tree (section 2)?
- Bump to the toolchain verso-blueprint supports, or pin verso-blueprint to 4.32.2?
- Does the blueprint cover only the Smith chain (M0-M8), or also the `OneSidedTM` class
  proofs, which live in the same `lean_lib`?
