# Wolfram (2,3) universality in Lean 4

A machine-checked development of Alex Smith's 2007 proof that Wolfram's 2-state
3-colour Turing machine emulates every two-colour cyclic tag system, extended by a
Cocke-Minsky reduction from binary Turing machines to cyclic tag systems.

Note: the Lake root is `Proofs/` inside the `TuringMachine` paclet repository; paths
below are relative to this directory.

## What is proved

`Smith.wolfram23_universal` (`Wolfram23/Universality/T8.lean`): for every well-formed
binary Turing machine `tm`, valid configuration `c` and run of `n` steps, there is a
finite tape from which `BiTM.wolfram23` reproduces the `n + 1` configurations of the
run, read off the tape by the decoder `Smith.decodeTM` at strictly increasing times,
with the run confined to the tape until it leaves it to the right in state A. This is
Smith's Conjecture 0 in finite form (T4, `Smith.conjecture0_finite`) composed with the
Cocke-Minsky reduction (T7).

`Smith.wolfram23_infinite` (`Wolfram23/Infinite/T6.lean`): the infinite form. For every
well-formed binary Turing machine `tm` and valid configuration `c` there is a
right-infinite tape of cells 0, 1, 2 from which `BiTM.wolfram23`, started at its left
end, runs for ever, never leaves the tape to the left, and for every `k` reproduces
the first `k` configurations of the run of the machine (as many of them as exist) at
strictly increasing times, read off a window of the tape by `Smith.decodeTM`. No
budget and no hypothesis on halting.

The same theorems with the tape in closed form, a definition that runs no system
(`Smith.wolfram23_universal_ic` on `Smith.IC tm c n`, `Smith.wolfram23_infinite_ic` on
`Smith.ITape tm c`), and loop-freeness (T5, `Smith.wolfram23_not_periodic`) are optional
corollaries in `Extras/`, outside the headline theorems' imports. The blueprint's
overview chapter states exactly what is and is not proved; its open-items chapter lists
the gaps.

## The chain, one module per rung

    binary TM -> 2-tag -> cyclic tag -> System 5 -> System 4 -> System 3 -> 2 -> 1 -> 0 = wolfram23

`Wolfram23.lean` imports the rungs; each rung is an entry module over a directory:

| Module | Contents |
|---|---|
| `Wolfram23.Systems` | `StepSys` (every system's step and iteration), `ForwardSim`, schedules |
| `Wolfram23.FiniteSets` | finite sets of integers as lists, `xorMerge` |
| `Wolfram23.Machines` | binary Turing machines and `wolfram23`, the lookahead machines (Systems 0 to 3), tag and cyclic tag systems |
| `Wolfram23.TMToTag` | rung 1: a binary machine by a 2-tag system (Cocke-Minsky) |
| `Wolfram23.TagToCTS` | rung 2: a 2-tag system by a cyclic tag system (Cook); T7 |
| `Wolfram23.CTSToSystem5` | rung 3: doubling, the `cy2s5.pl` encoder, `Represents`, T1 |
| `Wolfram23.System5ToSystem4` | rung 4: System 4, the `s52s4.pl` encoder, `RepS4`, T2 |
| `Wolfram23.System4ToSystem3` | rung 5: parity blocks, the runs of System 3, `Rep3`, T3 |
| `Wolfram23.System3ToWolfram23` | rung 6: the relabelings `phi3`, `phi2` (`sys3_sys0_forwardSim`) and the bridge to `BiTM.wolfram23` |
| `Wolfram23.Universality` | T4 (`conjecture0_finite`) and T8 (`wolfram23_universal`) |
| `Wolfram23.Infinite` | the raw runs, the guarded blocks and T6 (`wolfram23_infinite`) |

## Axiom check

```
cat > /tmp/ax.lean <<'EOF'
import Wolfram23
#print axioms Smith.wolfram23_universal
#print axioms Smith.wolfram23_infinite
EOF
lake env lean /tmp/ax.lean
```

Expected output:

```
'Smith.wolfram23_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Smith.wolfram23_infinite' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry` in `Wolfram23/` or `Extras/`; `native_decide` only in `Vectors/`, which
nothing imports.

## Build

Toolchain `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0` (pinned in `lake-manifest.json`).

```
lake exe cache get
lake build                 # the chain (and OneSidedTM)
lake build Extras Vectors  # the optional corollaries and the regression vectors
```

With the Mathlib cache the proofs take a few minutes.

## Where things are

- `Wolfram23/`: the chain (above). `Extras/`: T5 and the closed-form initial
  conditions. `Vectors/`: regression vectors against Smith's printed traces, a small
  machine, and blocks of the infinite tape; `scripts/ExportVectors.lean` writes the
  vectors the paclet's `Emulation.wlt` checks.
- `Blueprint/Chapters/`: the prose companion, one Verso chapter per link, with the
  statements linked to their declarations.
- `docs/PLAN.md`: targets T1 to T8 and the milestone notes M0 to M9, the engineering
  record (its file paths predate the per-rung layout). `docs/REVIEW.md`: the audit that
  preceded the rebuild, with status notes. `docs/PUBLISHING.md`: the publishing plan.
  `docs/TM23Proof.pdf`: Smith's paper.
- `OneSidedTM/`: an unrelated earlier development in the same `lean_lib` (classes of
  one-sided machines); not part of the chain.

## The blueprint site

The prose companion of the proof (one chapter per link of the chain, the statements
linked to their declarations, the dependency graph, the progress summary) is a Verso
blueprint. It is not built while verso-blueprint has no v4.36 branch (see
`lakefile.lean`); the published site stays up. When it returns it is `Blueprint.lean`, `Blueprint/Chapters/`, `BlueprintMain.lean`, rendered by

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
