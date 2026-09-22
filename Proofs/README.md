# Wolfram (2,3) universality in Lean 4

A machine-checked development of Alex Smith's 2007 proof that Wolfram's 2-state
3-colour Turing machine emulates every two-colour cyclic tag system, extended by a
Cocke-Minsky reduction from binary Turing machines to cyclic tag systems.

Note: the Lake root is `Proofs/` inside the `TuringMachine` paclet repository; paths
below are relative to this directory.

## What is proved

`Smith.wolfram23_universal_ic` (`Smith/Universality.lean`): for every well-formed binary
Turing machine `tm`, valid configuration `c` and run of `n` steps, `BiTM.wolfram23`
started on the finite tape `Smith.IC tm c n` reproduces the `n + 1` configurations of
the run, read off the tape by the decoder `Smith.decodeTM` at strictly increasing
times, with the run confined to the tape until it leaves it to the right in state A.
This is Smith's Conjecture 0 in finite form composed with the Turing-machine
reduction. `IC tm c n` is a definition: Smith's encoders applied to `tm`, `c` and `n`,
with parameters from closed-form bounds on the run lengths (`Smith/RunBounds.lean`,
`TagSystem/TagBounds.lean`, `Smith/ClosedForm.lean`); it runs no system.
`Smith.wolfram23_universal` is the corollary with the tape existential.

`Smith.wolfram23_infinite_ic` (`Smith/Infinite.lean`): the infinite form. For every
well-formed binary Turing machine `tm` and valid configuration `c`, the right-infinite
tape `Smith.ITape tm c` of cells 0, 1, 2 (again a definition) is one from which
`BiTM.wolfram23`, started at its left end, runs for ever, never leaves the tape to the
left, and for every `k` reproduces the first `k` configurations of the run of the
machine (as many of them as exist) at strictly increasing times, read off a window of
the tape by `Smith.decodeTM`. No budget and no hypothesis on halting.
`Smith.wolfram23_infinite` is the corollary with the tape existential.
The blueprint's overview chapter states exactly what is and is not proved; its
open-items chapter lists the gaps.

The chain, one module per arrow:

    binary TM -> 2-tag -> cyclic tag -> System 5 -> System 4 -> System 3 -> 2 -> 1 -> 0 = wolfram23

## Axiom check

```
cat > /tmp/ax.lean <<'EOF'
import Smith.Infinite
#print axioms Smith.wolfram23_universal_ic
#print axioms Smith.wolfram23_infinite_ic
EOF
lake env lean /tmp/ax.lean
```

Expected output:

```
'Smith.wolfram23_universal_ic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Smith.wolfram23_infinite_ic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry` in `Smith/`, `TagSystem/`, `BiTM/`, `TM/`; `native_decide` only in `Vectors/`,
which nothing imports.

## Build

Toolchain `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (pinned in `lake-manifest.json`).

```
lake exe cache get
lake build
```

A full build is about 870 jobs plus Verso; with the Mathlib cache the proofs take a few
minutes, Verso about a quarter of an hour the first time.

## Where things are

- `Blueprint/Chapters/`: the prose companion, one Verso chapter per link, with the
  statements linked to their declarations (the blueprint site above).
- `docs/PLAN.md`: targets T1 to T8 and the milestone notes M0 to M8 and M7, the
  engineering record. `docs/REVIEW.md`: the audit that preceded the rebuild, with status notes.
  `docs/PUBLISHING.md`: the publishing plan. `docs/TM23Proof.pdf`: Smith's paper.
- `Vectors/SmithVectors.lean`, `Vectors/TMToCTSVectors.lean`, `Vectors/InfiniteVectors.lean`:
  regression vectors against Smith's printed traces, a small machine, and a small block
  of the infinite tape.
- `OneSidedTM/`: an unrelated earlier development in the same `lean_lib` (classes of
  one-sided machines); not part of the chain.

## The blueprint site

The prose companion of the proof (one chapter per link of the chain, the statements
linked to their declarations, the dependency graph, the progress summary) is a Verso
blueprint: `Blueprint.lean`, `Blueprint/Chapters/`, `BlueprintMain.lean`, rendered by

```
lake exe vbp build            # to _out/site/html-multi
lake exe vbp build --serve    # local preview
```

It is published to GitHub Pages at <https://wolframinstitute.github.io/TuringMachine/>
by `.github/workflows/blueprint-pages.yml` (repository root) on every push that touches
`Proofs/`, and to the Wolfram Cloud by `scripts/CloudDeployBlueprint.wl`. See
`docs/PUBLISHING.md`.

## Codespaces

`.devcontainer/` fetches the Mathlib cache and builds on creation (Codespaces reads
`.devcontainer` at the repository root, so it is a template until moved there).
