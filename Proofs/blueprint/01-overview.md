# 01. Overview: what is proved

## Orientation

The headline theorem is `[[Smith.wolfram23_universal]]` in `Smith/Universality.lean`.
In one sentence: for every well-formed binary Turing machine, every valid configuration
and every finite run of `n` steps, there is a finite tape from which Wolfram's 2-state
3-colour machine (`[[BiTM.wolfram23]]`) reproduces the `n + 1` configurations of that
run, read off the tape by a fixed decoder at strictly increasing times, with the run
confined to the tape until it leaves it to the right in state A.

This is Smith's Conjecture 0 in its finite form (TM23Proof.pdf p. 4, "for an arbitrary
number of steps"), composed with a Cocke-Minsky reduction from Turing machines to
cyclic tag systems. The tape it exhibits depends on the run length. The infinite form
(one initial condition that emulates forever, p. 21-22) is
`[[Smith.wolfram23_infinite]]` in `Smith/Infinite.lean`: one right-infinite tape per
machine and input, from which wolfram23 runs for ever and reproduces every prefix of the
run of the machine; chapter 10 states it and describes its construction. Chapter 11
lists what remains open: the tapes of both theorems are existential, with no
closed-form size bound.

## The statement

```lean
theorem wolfram23_universal (tm : Machine) (hwf : WF tm) (c : Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) (n : Nat) (c' : Config) (hrun : BiTM.nSteps tm c n = some c') :
    ∃ (start : BiTM.Config) (w b : Nat) (times : Nat → Nat) (T : Nat),
      IsValidWolfram23Cfg start ∧ start.state = 1 ∧
      (∀ i, i < n → times i < times (i + 1)) ∧
      (∀ i, i ≤ n → times i ≤ T ∧
        ∃ ci cfgi, BiTM.nSteps tm c i = some ci ∧ BiTM.nSteps wolfram23 start (times i) = some cfgi ∧
          decodeTM tm.numStates (2 ^ w) b cfgi = some (canon ci)) ∧
      (∀ τ, τ ≤ T → ∃ cfgτ, BiTM.nSteps wolfram23 start τ = some cfgτ ∧ biSize cfgτ = biSize start) ∧
      (∃ L : List Nat, BiTM.nSteps wolfram23 start (T + 1) = some ⟨1, L, 0, []⟩ ∧
        L.length = biSize start)
```

Read clause by clause:

- `tm : Machine` is a Turing machine in the shared model of `TM/Defs.lean`
  (`[[TM.Machine]]`): states and symbols are natural numbers, state 0 halts.
  `[[TagSystem.WF]]` says that from a state below `numStates`, reading a bit, the
  machine writes a bit and moves to a state below `numStates`. `[[TagSystem.ValidCfg]]`
  says the tape of `c` holds bits. So the class of machines is the binary machines,
  not all machines (chapter 03 and chapter 11).
- `hrun` gives the run of `n` steps that is to be reproduced. The tape `start` is chosen
  after `n` and `hrun`: it is one tape per machine, configuration and budget.
- `start` is a `[[BiTM.Config]]` (chapter 02): a finite zipper with implicit blanks on
  both sides, valid (`[[BiTM.IsValidWolfram23Cfg]]`: states A or B, symbols 0, 1, 2) and
  in state A (`state = 1`).
- `times` is a strictly increasing schedule on `[0, n]`, all below the exit time `T`.
  At time `times i` the wolfram23 configuration decodes, by
  `[[Smith.decodeTM]] tm.numStates (2 ^ w) b`, to `[[TagSystem.canon]] ci`, the `i`-th
  configuration of the run without trailing blanks. The decoder is a fixed function of
  three parameters (the number of states, the block width `2^w`, the band `b`); it does
  not see `tm`, `c` or the run.
- Confinement: up to time `T` the number of explicit cells, `[[Smith.biSize]]`, never
  changes. A wolfram23 step onto an implicit blank grows the explicit tape by one cell,
  so this says the head never leaves the initial tape before `T`.
- Exit: at time `T + 1` the head is on the cell right of the tape, a 0, in state A, and
  the tape has grown by exactly that cell. This is the exit condition of Smith's
  Conjecture 0 (p. 4: "the first cell to become active after the emulation has
  finished is the cell to the right of the initial condition, and ... it becomes active
  in state A").

## What it does not say

- The tape `start`, the width `w` and the band `b` are existential. The proof chooses
  them from the run lengths of the emulating systems (chapter 08 lists the choices), not
  from a closed-form bound on the machine's run. No size or complexity bound on `start`
  is stated. Smith's answer to "is the initial condition doing the computation" (his
  finish-time bound and the non-universal constructor of p. 20-26) has no counterpart
  yet. This is the main finding of the independent review (chapter 11).
- The times are existential. Nothing in the statement lets an observer of the wolfram23
  run locate `times i`, and nothing is said about what the decoder returns at other
  times.
- Machines are binary. The reduction of k-symbol machines to binary machines is not
  formalized.
- The decoder recovers configurations up to trailing blanks (`canon`).
- The infinite form is `[[Smith.wolfram23_infinite]]` (chapter 10): one tape per machine
  and input, no budget; its block sizes are existential too.

## The chain

Each arrow is a forward simulation (`[[Smith.ForwardSim]]`, chapter 04 for the calculus)
or a functional relabeling, proved in the module named under it.

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
`[[Smith.conjecture0_finite]]` (chapter 08); the composition with the Turing machine
half is chapter 09.

## Axiom check

```
$ cat > /tmp/ax.lean <<'EOF'
import Smith.Universality
#print axioms Smith.wolfram23_universal
EOF
$ lake env lean /tmp/ax.lean
'Smith.wolfram23_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same three axioms for `[[Smith.conjecture0_finite]]`, `[[TagSystem.t7_finite]]`,
`[[Smith.sys4_sys3_forwardSim]]`, `[[Smith.conjecture4_finite]]`,
`[[Smith.conjecture5_finite_exact]]` and `[[Smith.sys3_sys0_forwardSim]]`. No `sorry`
anywhere in `Smith/`, `TagSystem/`, `BiTM/`, `TM/`; `native_decide` only in `Tests/`,
which nothing imports.

## How to read this blueprint

Chapters 02 to 09 follow the chain from the Turing machine to wolfram23, which is the
order of the composition, not the order in which the links were proved (that order is
in `docs/PLAN.md` section 5). Each chapter has: an orientation paragraph; the
mathematics in prose with formal names in wiki links; the key statements quoted from
the source; notes and caveats. A reader checking a single link needs only that chapter,
its module, and chapter 02 for the machine model. Chapter 10 was written as a
specification before its proof and reconciled with the source when the theorem landed;
chapter 11 is the list of debts.
