/-
  Blueprint.Chapters.Overview

  Chapter 1 of the blueprint: what is proved. The two headline statements
  (closed-form initial conditions) and their existential corollaries
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

The headline theorem is {bpref "Smith.wolfram23_universal_ic"}[`Smith.wolfram23_universal_ic`] in [`Smith/Universality.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Universality.lean).
In one sentence: for every well-formed binary Turing machine `tm`, every valid
configuration `c` and every finite run of `n` steps, Wolfram's 2-state 3-colour
machine ({bpref "BiTM.wolfram23"}[`BiTM.wolfram23`]) started on the finite tape `IC tm c n` reproduces the `n + 1`
configurations of that run, read off the tape by a fixed decoder at strictly
increasing times, with the run confined to the tape until it leaves it to the right
in state A. `IC tm c n` is a definition, computed from `tm`, `c` and `n` by the
encoders and by closed-form bounds on the run lengths; it runs neither the machine
nor any of the emulating systems.

This is Smith's Conjecture 0 in its finite form (p. 4, "for an arbitrary number of
steps"), composed with a Cocke-Minsky reduction from Turing machines to cyclic tag
systems. The tape depends on the number of steps `n`. The infinite form (one
initial condition that emulates forever, p. 21-22) is {bpref "Smith.wolfram23_infinite_ic"}[`Smith.wolfram23_infinite_ic`] in
[`Smith/Infinite.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Infinite.lean): one right-infinite tape `ITape tm c` per machine and input, again a
definition, from which wolfram23 runs for ever and reproduces every prefix of the
run of the machine; the chapter on the infinite form describes its construction.
Both have corollaries with the tape existential,
{bpref "Smith.wolfram23_universal"}[`Smith.wolfram23_universal`] and {bpref "Smith.wolfram23_infinite"}[`Smith.wolfram23_infinite`]. The chapter on open items lists
what remains open.

# The statements

:::group "headline"
The two headline theorems: the finite form (one tape per machine, input and
budget) and the infinite form (one tape per machine and input), both with the
initial condition in closed form, and their corollaries with the tape
existential.
:::

:::theorem "Smith.wolfram23_universal_ic" (parent := "headline") (lean := "Smith.wolfram23_universal_ic") (tags := "headline, T8")
For a well-formed binary Turing machine `tm` ({uses "TagSystem.WF"}[]), a valid configuration
`c` ({uses "TagSystem.ValidCfg"}[]) with state below `numStates`, and a run of `n` steps of `tm`
from `c`, let `start = IC tm c n` ({uses "Smith.IC"}[]), `w = ICw tm c n` and
`b = ICb tm c n`. There are times `times i` and an exit time `T` such that: `start`
is valid and in state A; the times are strictly increasing on `[0, n]` and below `T`;
at time `times i` the wolfram23 configuration decodes by {uses "Smith.decodeTM"}[] with the
parameters `numStates`, `2^w`, `b` to the `i`-th configuration of the run without
trailing blanks ({uses "TagSystem.canon"}[]); up to time `T` the explicit tape keeps its
size ({uses "Smith.biSize"}[]); and at time `T + 1` the head is on the cell right of the
tape, a 0, in state A.
:::

:::theorem "Smith.wolfram23_universal" (parent := "headline") (lean := "Smith.wolfram23_universal") (tags := "T8")
The same with `start`, `w` and `b` existential: for `tm`, `c` and a run of `n`
steps as in {uses "Smith.wolfram23_universal_ic"}[] there are a wolfram23 configuration
`start`, a block width `2^w`, a band `b`, times and an exit time with the same five
clauses.
:::

:::proof "Smith.wolfram23_universal"
{uses "Smith.wolfram23_universal_ic"}[] with `start = IC tm c n`.
:::

Read clause by clause:

- `tm : Machine` is a Turing machine in the shared model of [`TM/Defs.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/TM/Defs.lean)
  ({bpref "TM.Machine"}[]): states and symbols are natural numbers, state 0 halts.
  {bpref "TagSystem.WF"}[`TagSystem.WF`] says that from a state below `numStates`, reading a bit, the machine
  writes a bit and moves to a state below `numStates`. {bpref "TagSystem.ValidCfg"}[`TagSystem.ValidCfg`] says the
  tape of `c` holds bits. So the class of machines is the binary machines, not all
  machines (the chapters on the machine reduction and on open items).
- `hrun` gives the run of `n` steps that is to be reproduced. The tape
  `start = IC tm c n` depends on `n` but not on `hrun`: it is one tape per machine,
  configuration and budget, written down from `tm`, `c` and `n` alone (the chapter
  on the composition gives its construction).
- `start` is a {bpref "BiTM.Config"}[`BiTM.Config`]: a finite zipper with implicit
  blanks on both sides, valid ({bpref "BiTM.IsValidWolfram23Cfg"}[`BiTM.IsValidWolfram23Cfg`]: states A or B, symbols 0,
  1, 2) and in state A (`state = 1`).
- `times` is a strictly increasing schedule on `[0, n]`, all below the exit time `T`.
  At time `times i` the wolfram23 configuration decodes, by
  `Smith.decodeTM tm.numStates (2 ^ w) b`, to `TagSystem.canon ci`, the `i`-th
  configuration of the run without trailing blanks. The decoder is a fixed function
  of three parameters (the number of states, the block width `2^w`, the band `b`); it
  does not see `tm`, `c` or the run.
- Confinement: up to time `T` the number of explicit cells, {bpref "Smith.biSize"}[`Smith.biSize`], never
  changes. A wolfram23 step onto an implicit blank grows the explicit tape by one
  cell, so this says the head never leaves the initial tape before `T`.
- Exit: at time `T + 1` the head is on the cell right of the tape, a 0, in state A,
  and the tape has grown by exactly that cell. This is the exit condition of Smith's
  Conjecture 0 (p. 4: "the first cell to become active after the emulation has
  finished is the cell to the right of the initial condition, and ... it becomes
  active in state A").

:::theorem "Smith.wolfram23_infinite_ic" (parent := "headline") (lean := "Smith.wolfram23_infinite_ic") (tags := "headline, T6")
For a well-formed binary machine `tm` and a valid configuration `c` with state below
`numStates`, the right-infinite tape `ITape tm c` ({uses "Smith.ITape"}[]) has cells 0, 1,
2, and from {uses "Smith.istart"}[] `(ITape tm c)` (state B on a 2, nothing to the left,
the tape to the right) at every time the run of wolfram23 is defined and does not
move left from an empty left tape; for every `k` there are a window `W` and strictly
increasing times, the last later than `k`, such that at time `times i` for `i <= k`
wolfram23 is in state B and, whenever the `i`-th configuration of the run exists, the
cells right of the head, on the window `W` and on every larger window, decode by
{uses "Smith.decodeTM"}[] with the width `2 ^ blkW tm c k` and the band
`icBand (blkProg tm c k)` of block `k` to that configuration.
:::

:::theorem "Smith.wolfram23_infinite" (parent := "headline") (lean := "Smith.wolfram23_infinite") (tags := "T6")
The same with the tape, the widths and the bands existential (and the times
required to increase only while the run of `tm` goes on): there is one
right-infinite tape `t` of cells 0, 1, 2 with the clauses of
{uses "Smith.wolfram23_infinite_ic"}[].
:::

:::proof "Smith.wolfram23_infinite"
{uses "Smith.wolfram23_infinite_ic"}[] with `t = ITape tm c`.
:::

The infinite form has no budget and no hypothesis on halting. Its tape is one object
per machine and input; the parameters and the schedule vary with `k`, as in Smith's
construction, and block `k` is a closed form of `tm`, `c` and `k`. The chapter on
the infinite form reads it clause by clause.

# What the statements do not say

- The tapes are definitions, but no bound on their size or on the cost of writing
  them down is stated as a theorem. They are large: the budget of `IC tm c n` is
  `n * 15 * 2 ^ (sz c + n)` cycles of a cyclic tag system with `2 (1 + 84 S)`
  appendants, and the parameters grow exponentially in the number of System 5
  rules (the chapter on Conjecture 0 lists them). That they are computed without
  running anything is Smith's answer (p. 20-26) to "is the initial condition doing
  the computation".
- The times are existential. Nothing in the statement lets an observer of the
  wolfram23 run locate `times i`, and nothing is said about what the decoder returns
  at other times.
- Machines are binary. The reduction of k-symbol machines to binary machines is not
  formalized.
- The decoder recovers configurations up to trailing blanks (`canon`).
- The conclusions alone are also met by a machine that only moves right over a tape
  holding the run in advance. What rules this out for wolfram23 is that the tape is
  the stated definition `IC tm c n` (or `ITape tm c`), built by Smith's encoders
  from the machine's description and the closed-form bounds, which never compute
  the run.

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
{bpref "Smith.conjecture0_closed"}[]; the composition with the Turing machine half is the
chapter on the composition.

# Axiom check

```
$ cat > /tmp/ax.lean <<'EOF'
import Smith.Infinite
#print axioms Smith.wolfram23_universal_ic
#print axioms Smith.wolfram23_infinite_ic
EOF
$ lake env lean /tmp/ax.lean
'Smith.wolfram23_universal_ic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Smith.wolfram23_infinite_ic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same three axioms for the corollaries {bpref "Smith.wolfram23_universal"}[] and
{bpref "Smith.wolfram23_infinite"}[], for {bpref "Smith.conjecture0_closed"}[], {bpref "TagSystem.t7_finite"}[],
{bpref "Smith.sys4_sys3_forwardSim"}[], {bpref "Smith.conjecture4_finite"}[],
{bpref "Smith.conjecture5_finite_exact"}[] and {bpref "Smith.sys3_sys0_forwardSim"}[]. No `sorry`
anywhere in [`Smith/`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/), [`TagSystem/`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/TagSystem/), [`BiTM/`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/BiTM/), [`TM/`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/TM/); `native_decide` only in [`Vectors/`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/),
which nothing imports.

# How to read this blueprint

The chapters from the machine model to the composition follow the chain from the
Turing machine to wolfram23, which is the order of the composition, not the order in
which the links were proved (that order is in [`docs/PLAN.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/PLAN.md) section 5). Each chapter
has: an orientation paragraph; the mathematics in prose with the formal statements
linked to their declarations; notes and caveats. A reader checking a single link
needs only that chapter, its module, and the chapter on the machine model. The
chapter on open items lists what is not proved.
