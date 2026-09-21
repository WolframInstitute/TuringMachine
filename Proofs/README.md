# Wolfram (2,3) universality in Lean 4

A machine-checked development of Alex Smith's 2007 proof that Wolfram's 2-state
3-colour Turing machine emulates every two-colour cyclic tag system, extended by a
Cocke-Minsky reduction from binary Turing machines to cyclic tag systems.

Note: the Lake root is `Proofs/` inside the `TuringMachine` paclet repository. Whether
to split it into its own repository is an open question (`docs/PUBLISHING.md`
section 2); paths below are relative to this directory and would survive a split.

## What is proved

`Smith.wolfram23_universal` (`Smith/Universality.lean`): for every well-formed binary
Turing machine, valid configuration and run of `n` steps, there is a finite tape from
which `BiTM.wolfram23` reproduces the `n + 1` configurations of the run, read off the
tape by the decoder `Smith.decodeTM` at strictly increasing times, with the run confined
to the tape until it leaves it to the right in state A. This is Smith's Conjecture 0 in
finite form composed with the Turing-machine reduction. The tape is existential and
depends on the budget `n`.

`Smith.wolfram23_infinite` (`Smith/Infinite.lean`): the infinite form. For every
well-formed binary Turing machine and valid configuration there is one right-infinite
tape of cells 0, 1, 2 from which `BiTM.wolfram23`, started at its left end, runs for
ever, never leaves the tape to the left, and for every `k` reproduces the first `k`
configurations of the run of the machine (as many of them as exist) at strictly
increasing times, read off a window of the tape by `Smith.decodeTM`. No budget and no
hypothesis on halting; the block sizes are still existential.
`blueprint/01-overview.md` states exactly what is and is not proved;
`blueprint/11-open-items.md` lists the gaps.

The chain, one module per arrow:

    binary TM -> 2-tag -> cyclic tag -> System 5 -> System 4 -> System 3 -> 2 -> 1 -> 0 = wolfram23

## Axiom check

```
cat > /tmp/ax.lean <<'EOF'
import Smith.Infinite
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

No `sorry` in `Smith/`, `TagSystem/`, `BiTM/`, `TM/`; `native_decide` only in `Tests/`,
which nothing imports.

## Build

Toolchain `leanprover/lean4:v4.32.2`, Mathlib pinned in `lake-manifest.json`.

```
lake exe cache get
lake build
```

A full build is about 850 jobs; with the Mathlib cache it takes a few minutes.

## Where things are

- `blueprint/`: the prose companion, one chapter per link, with the formal statements
  quoted (Markdown now, Verso port pending).
- `docs/PLAN.md`: targets T1 to T8 and the milestone notes M0 to M8 and M7, the
  engineering record. `docs/REVIEW.md`: the audit that preceded the rebuild, with status notes.
  `docs/PUBLISHING.md`: the publishing plan. `docs/TM23Proof.pdf`: Smith's paper.
- `Tests/SmithVectors.lean`, `Tests/TMToCTSVectors.lean`, `Tests/InfiniteVectors.lean`:
  regression vectors against Smith's printed traces, a small machine, and a small block
  of the infinite tape.
- `OneSidedTM/`: an unrelated earlier development in the same `lean_lib` (classes of
  one-sided machines); not part of the chain.

## Codespaces

[Open in GitHub Codespaces](https://codespaces.new/sw1sh/TuringMachine) (badge and
target to be set once the repository layout is decided). `.devcontainer/` fetches the
Mathlib cache and builds on creation.
