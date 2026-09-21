/-
  Blueprint.Chapters.Overview

  Chapter 1 of the blueprint: what is proved. The two headline statements
  are introduced here (their proofs are in the chapters on the composition
  and on the infinite form), with the reading of each clause, what the
  statements do not say, the chain, and the axiom check.
-/

import Verso
import VersoManual
import VersoBlueprint
import Smith.Universality
import Smith.Infinite

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Overview: what is proved" =>

%%%
tag := "overview"
file := "overview"
htmlSplit := .never
%%%

# Orientation

The headline theorem is `Smith.wolfram23_universal` in `Smith/Universality.lean`.
In one sentence: for every well-formed binary Turing machine, every valid
configuration and every finite run of `n` steps, there is a finite tape from which
Wolfram's 2-state 3-colour machine (`BiTM.wolfram23`) reproduces the `n + 1`
configurations of that run, read off the tape by a fixed decoder at strictly
increasing times, with the run confined to the tape until it leaves it to the right
in state A.

This is Smith's Conjecture 0 in its finite form (p. 4, "for an arbitrary number of
steps"), composed with a Cocke-Minsky reduction from Turing machines to cyclic tag
systems. The tape it exhibits depends on the run length. The infinite form (one
initial condition that emulates forever, p. 21-22) is `Smith.wolfram23_infinite` in
`Smith/Infinite.lean`: one right-infinite tape per machine and input, from which
wolfram23 runs for ever and reproduces every prefix of the run of the machine; the
chapter on the infinite form describes its construction. The chapter on open items
lists what remains open: the tapes of both theorems are existential, with no
closed-form size bound.

# The statements

:::group "headline"
The two headline theorems: the finite form (one tape per machine, input and
budget) and the infinite form (one tape per machine and input).
:::

:::theorem "Smith.wolfram23_universal" (parent := "headline") (lean := "Smith.wolfram23_universal") (tags := "headline, T8")
For a well-formed binary Turing machine `tm` ({uses "TagSystem.WF"}[]), a valid configuration
`c` ({uses "TagSystem.ValidCfg"}[]) with state below `numStates`, and a run of `n` steps of `tm`
from `c`, there are a wolfram23 configuration `start`, a block width `2^w`, a band
`b`, times `times i` and an exit time `T` such that: `start` is valid and in state A;
the times are strictly increasing on `[0, n]` and below `T`; at time `times i` the
wolfram23 configuration decodes by {uses "Smith.decodeTM"}[] with the parameters
`numStates`, `2^w`, `b` to the `i`-th configuration of the run without trailing
blanks ({uses "TagSystem.canon"}[]); up to time `T` the explicit tape keeps its size
({uses "Smith.biSize"}[]); and at time `T + 1` the head is on the cell right of the tape,
a 0, in state A.
:::

Read clause by clause:

- `tm : Machine` is a Turing machine in the shared model of `TM/Defs.lean`
  ({bpref "TM.Machine"}[]): states and symbols are natural numbers, state 0 halts.
  `TagSystem.WF` says that from a state below `numStates`, reading a bit, the machine
  writes a bit and moves to a state below `numStates`. `TagSystem.ValidCfg` says the
  tape of `c` holds bits. So the class of machines is the binary machines, not all
  machines (the chapters on the machine reduction and on open items).
- `hrun` gives the run of `n` steps that is to be reproduced. The tape `start` is
  chosen after `n` and `hrun`: it is one tape per machine, configuration and budget.
- `start` is a `BiTM.Config` ({bpref "BiTM.Config"}[]): a finite zipper with implicit
  blanks on both sides, valid (`BiTM.IsValidWolfram23Cfg`: states A or B, symbols 0,
  1, 2) and in state A (`state = 1`).
- `times` is a strictly increasing schedule on `[0, n]`, all below the exit time `T`.
  At time `times i` the wolfram23 configuration decodes, by
  `Smith.decodeTM tm.numStates (2 ^ w) b`, to `TagSystem.canon ci`, the `i`-th
  configuration of the run without trailing blanks. The decoder is a fixed function
  of three parameters (the number of states, the block width `2^w`, the band `b`); it
  does not see `tm`, `c` or the run.
- Confinement: up to time `T` the number of explicit cells, `Smith.biSize`, never
  changes. A wolfram23 step onto an implicit blank grows the explicit tape by one
  cell, so this says the head never leaves the initial tape before `T`.
- Exit: at time `T + 1` the head is on the cell right of the tape, a 0, in state A,
  and the tape has grown by exactly that cell. This is the exit condition of Smith's
  Conjecture 0 (p. 4: "the first cell to become active after the emulation has
  finished is the cell to the right of the initial condition, and ... it becomes
  active in state A").

:::theorem "Smith.wolfram23_infinite" (parent := "headline") (lean := "Smith.wolfram23_infinite") (tags := "headline, T6")
For a well-formed binary machine `tm` and a valid configuration `c` with state below
`numStates` there is one right-infinite tape `t` of cells 0, 1, 2 such that, from
{uses "Smith.istart"}[] `t` (state B on a 2, nothing to the left, `t` to the right), at
every time the run of wolfram23 is defined and does not move left from an empty
left tape, and for every `k` there are a width `2^w`, a band `b`, a window `W` and
times, the last later than `k`, strictly increasing as long as the run of `tm` goes
on, such that at time `times i` for `i <= k` wolfram23 is in state B and the cells
right of the head, on the window `W` and on every larger window, decode by
{uses "Smith.decodeTM"}[] to the `i`-th configuration of the run whenever it exists.
:::

The infinite form has no budget and no hypothesis on halting. Its tape is one object
per machine and input; the parameters and the schedule vary with `k`, as in Smith's
construction, and its block sizes are existential too. The chapter on the infinite
form reads it clause by clause.

# What the statements do not say

- The tape `start`, the width `w` and the band `b` are existential. The proof chooses
  them from the run lengths of the emulating systems (the chapter on Conjecture 0
  lists the choices), not from a closed-form bound on the machine's run. No size or
  complexity bound on `start` is stated. Smith's answer to "is the initial condition
  doing the computation" (his finish-time bound and the non-universal constructor of
  p. 20-26) has no counterpart yet. This is the main finding of the independent review
  (the chapter on open items).
- The times are existential. Nothing in the statement lets an observer of the
  wolfram23 run locate `times i`, and nothing is said about what the decoder returns
  at other times.
- Machines are binary. The reduction of k-symbol machines to binary machines is not
  formalized.
- The decoder recovers configurations up to trailing blanks (`canon`).
- Neither statement bounds the work of the encoder: the conclusions are also met by a
  machine that only moves right over a tape holding the run in advance. What
  distinguishes wolfram23 is the construction inside the proofs (Smith's encoders).

# The chain

Each arrow is a forward simulation ({bpref "Smith.ForwardSim"}[], the chapter on cyclic tag
to System 5 for the calculus) or a functional relabeling, proved in the module named
under it.

```
binary TM  -->  2-tag  -->  cyclic tag  -->  System 5  -->  System 4  -->  System 3
  TagSystem/CockeMinsky   TagSystem/TagToCTS   Smith/Conjecture5   Smith/Conjecture4   Smith/Conjecture3
  TagSystem/TMToCTS                            Smith/ConjectureFive Smith/System4Runs   Smith/ParityBlocks
                                                                                        Smith/System3Runs

System 3  -->  System 2  -->  System 1  -->  System 0  ==  wolfram23
        Smith/Systems123 (phi3, phi2, 1-or-3 steps)    Smith/Wolfram23Bridge (toBi)
```

Systems 5 to 0 are Smith's (p. 3-5 and p. 32-35). System 0 is Wolfram's machine in
Smith's notation. The composition of the cyclic-tag-to-wolfram23 half is
{bpref "Smith.conjecture0_finite"}[]; the composition with the Turing machine half is the
chapter on the composition.

# Axiom check

```
$ cat > /tmp/ax.lean <<'EOF'
import Smith.Infinite
#print axioms Smith.wolfram23_universal
#print axioms Smith.wolfram23_infinite
EOF
$ lake env lean /tmp/ax.lean
'Smith.wolfram23_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Smith.wolfram23_infinite' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same three axioms for {bpref "Smith.conjecture0_finite"}[], {bpref "TagSystem.t7_finite"}[],
{bpref "Smith.sys4_sys3_forwardSim"}[], {bpref "Smith.conjecture4_finite"}[],
{bpref "Smith.conjecture5_finite_exact"}[] and {bpref "Smith.sys3_sys0_forwardSim"}[]. No `sorry`
anywhere in `Smith/`, `TagSystem/`, `BiTM/`, `TM/`; `native_decide` only in `Vectors/`,
which nothing imports.

# How to read this blueprint

The chapters from the machine model to the composition follow the chain from the
Turing machine to wolfram23, which is the order of the composition, not the order in
which the links were proved (that order is in `docs/PLAN.md` section 5). Each chapter
has: an orientation paragraph; the mathematics in prose with the formal statements
linked to their declarations; notes and caveats. A reader checking a single link
needs only that chapter, its module, and the chapter on the machine model. The
chapter on the infinite form was written as a specification before its proof and
reconciled with the source when the theorem landed; the chapter on open items is
the list of debts.
