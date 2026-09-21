# 10. T6: the infinite form

## Orientation

Smith's theorem, as he states it (TM23Proof.pdf p. 3 and p. 21-22), is the infinite
form: a single right-infinite initial condition from which System 0 emulates a
two-colour cyclic tag system for an infinite number of steps. The finite form of
chapter 08 is his Conjecture 0; the infinite form is what he calls the solution of the
problem posed in the introduction, and it is the form that answers the objection of
chapter 09 that a budget-indexed family of tapes is not one encoding.

This chapter states what is proved (`Smith/Infinite.lean`, `Smith/Guards.lean`,
2026-09-22), describes the construction, and says what remains existential. The
narrative was written before the proof and guided it; the sections below were
reconciled with the source when the theorem landed.

## The statement

`[[Smith.wolfram23_infinite]]`:

```lean
theorem wolfram23_infinite (tm : Machine) (hwf : WF tm) (c : Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) :
    ∃ t : Nat → Nat, (∀ i, t i < 3) ∧
      (∀ τ, ∃ d, inSteps wolfram23 (istart t) τ = some d ∧
        (d.left = [] → (wolfram23.transition d.state d.head).dir = Dir.R)) ∧
      ∀ k, ∃ (w b W : Nat) (times : Nat → Nat), k < times k ∧
        (∀ i, i < k → (BiTM.nSteps tm c (i + 1)).isSome → times i < times (i + 1)) ∧
        (∀ i ci, i ≤ k → BiTM.nSteps tm c i = some ci → ∃ d,
          inSteps wolfram23 (istart t) (times i) = some d ∧ d.state = 2 ∧
          ∀ W', W ≤ W' → decodeTM tm.numStates (2 ^ w) b (truncI W' d) = some (canon ci))
```

Read clause by clause:

- `tm`, `hwf`, `c`, `hv`, `hst` are as in chapter 01: a well-formed binary machine and
  a valid configuration with state in range. There is no budget and no hypothesis on
  halting.
- `t : Nat -> Nat` is the tape right of the head, a stream of cells, all 0, 1 or 2.
  `[[Smith.istart]] t` is the configuration `(state B, left [], head 2, right t)`: the
  head on a 2 in state B at the left end. `[[Smith.IConfig]]` is a wolfram23
  configuration whose right tape is a stream; `[[Smith.istep]]` and `[[Smith.inSteps]]`
  are `BiTM.step` and `BiTM.nSteps` with the stream in place of the list (the left tape
  is a list with an implicit blank beyond, as in `BiTM.Config`).
- At every time the run is defined (`[[Smith.inSteps_valid]]`: wolfram23 never halts on
  a configuration whose cells are below 3, `[[Smith.IValid]]`) and does not move left
  from an empty left tape: the head never leaves the tape to the left, so the implicit
  blank on the left is never read and the tape is genuinely one-sided.
- For every `k`: a width `2^w`, a band `b`, a window `W` and times `times i`, the last
  of them later than `k` (the emulation advances along the tape). The times are strictly
  increasing on `i < k` for as long as the run of `tm` continues (if `tm` halts at step
  `m < k`, the clause is silent beyond `m`; in the proof the times are constant there).
  For every `i <= k` at which the run of `tm` is defined, wolfram23 is in state B at
  `times i` and the infinite configuration, truncated to the `W` cells right of the
  head (`[[Smith.truncI]]`) or to any larger window, decodes by `[[Smith.decodeTM]]`
  (chapter 09) to the `i`-th configuration without trailing blanks
  (`[[TagSystem.canon]]`). The "any larger window" clause says that the decoder, which
  reads up to the first 0 right of the head, has read the whole leading conglomerate:
  the window does not cut it.

One tape per machine and input, with no budget in the statement. The parameters `w`,
`b`, `W` and the schedule vary with `k`, as in Smith's construction (his `w_n` grows
along the tape, p. 25): block `k` re-emulates the run from the start with its own width
and band, so the decode of step `i` recurs in every block `k >= i`. What the statement
does not say is discussed under "What remains existential" below.

## Smith's argument and why the finite T4 does not chain

Smith (p. 22): concatenate the initial condition that emulates the cyclic tag system for
1 step with the one for 2 steps, for 3 steps, and so on, and start with the leftmost 0 of
the first initial condition active in state A. Each finite emulation runs, exits to the
right onto the next initial condition's leftmost cell, a 0, in state A, and that is the
start condition of the next emulation. Any increasing sequence of budgets works, and
"what is in the initial tape to the left of that doesn't matter, as it never becomes
active." He needs loop-freeness (T5, chapter 07) only to know that each finite emulation
does exit; with the explicit schedules of chapters 04 to 08 the exit time is known and
T5 is not used.

The formal T4 does not chain by plain concatenation:

- Its head starts on the first cell of the first block, with the left end `0^m 2 2 1`
  to its left. Started on the leftmost 0 in state A, wolfram23 does `A0 -> 1RB`,
  `B0 -> 2LA`, `A1 -> 2LA` and is left of its starting cell after three steps.
- Smith's own Perl encoder has the same left end and he says so (p. 25-26): the
  `0^m 2 2 1` form "works, but doesn't allow the program to be chained after another
  program by concatenation." His concatenable left end (p. 12-13) is a sequence of
  repetitions `0 2^(2^w - 1)`, which the entering head converts to `2 2 1 2 1 ... 2 1 0`
  and which then supplies one turn per repetition.

So the blocks of the infinite tape are not T4's tapes.

## The construction

The key observation is that Smith's concatenable left end is, in System 4 terms, a row
of guard sets separated by stars in front of the encoder tape, and that the hand-off
between blocks is nothing but System 4's rule 5: the exit of a block leaves the head on
the next block's leading star in state C, and rule 5 carries it onto the first guard
set. So the infinite construction lives at the System 4 level and the System 3 relation
of chapter 06 only has to tolerate arbitrary cells beyond the guards.

### The block on the System 4 side (`Smith/Guards.lean`)

A block with guard parameter `n` and `r` guards is the tape `[[Smith.blockTape]] n r orig`:

    star, ({1, n}, star)^(r - 1), {0, 1, n - 1}, orig

where `orig = set S0 :: rest` is the encoder tape of chapter 05 for the program of the
block (`[[Smith.preGuardPairs]]`, `[[Smith.preM]]`). The head arrives on the leading star
in state C. Rule 5 toggles 1 in the first guard (giving `{n}`), the scan in state C
decrements it (giving `{n - 1}`, the state staying C because 0 is absent), rule 5 again
on the next star, and so on; the innermost `{0, 1, n - 1}` becomes `{0, n - 1}` and its
scan in state C toggles the state to B and decrements it. After `2r` steps the head is on
the program's first set in state B (`[[Smith.entryRun]]`, `[[Smith.padCfg_entry]]`): the
tape is now `star, ({n - 1}, star)^(r - 1), {n - 2}, orig` with the head on `orig`, which
is `[[Smith.padCfg]] n r 0 [star] [] (orig after its first step)`.

```lean
def padCfg (n r t : Nat) (Lc Rc : List System4Elem) (c : System4Config) : System4Config :=
  ⟨Lc ++ guardPairs n (r - 1 - t) ++ sets (merged n t) ++ c.elems ++ Rc,
   Lc.length + 2 * (r - 1 - t) + (t + 1) + c.active, c.state⟩
```

`[[Smith.guardPairs]] n k` is `k` copies of `{n - 1}` followed by a star; `[[Smith.merged]]
n t` is the list of sets right of the last remaining star after `t` turns: the `t`
guards whose stars were deleted, each decremented once per turn since, and the innermost
`{n - 2 - t}`. A turn of the program (rule 1 at its leftmost element, state A) becomes,
on the guarded tape, a walk left over the merged sets, the deletion of the next star
(rule 2, state B) and a scan of the merged sets, none of which contains 0 while
`t + 3 <= n` (`[[Smith.parMem_zero_merged]]`), so the head arrives back on the program's
first element in state B, exactly as the turn would have left it: `2t + 4` steps after
`t` turns (`[[Smith.pad_turn]]`). Every other rule is one step on both tapes
(`[[Smith.pad_step]]`). `[[Smith.pad_schedule]]` gives the padded run with its schedule and
the number of turns so far; before each turn at least one guard pair remains (`pad_turn`
needs `t + 2 <= r`, and `t <= N - 1 <= r - 2` for a program run of `N <= r - 1` steps),
the leading star is never deleted, and the head is never on it after time 0 (`PosRun`,
the `SafeC` condition of chapter 06); with `r = T4 + 1` and `N = T4 - 1` one pair is
still left after the last possible turn.

`[[Smith.block_run]]` is the block's System 4 run from its entry: the exit configuration
`padCfg n r (turns (T4 - 1)) [star] [] cE` at time `H`, where `cE` is the program's exit
(state C, head past the last element, chapter 05) and `T4` the length of the program's
run; `SafeC` for every budget; and the pop events of chapter 05 at the times
`2r + padT i`. `[[Smith.system4_emulation]]` (`Smith/Conjecture0.lean`, the System 4 half
of T4 factored out) supplies the program: for the cyclic tag run of `tt k` cycles it
gives the encoder tape, the exit, and the decoding events with their decodes.

`[[Smith.BlockData]]` packages a block: `n`, `r`, `w`, `b`, the program `S0`, `rest`, the
run length `H` and the decoding times `dt`; `[[Smith.BlockSpec]] tm c k bd` is the
specification a block must meet to emulate the first `k` steps (well-formedness of the
program, `n < 2^w`, `H + b + 3 <= 2^w`, integers below `2^w`, `SafeC (H + b)`, the exit,
the strictly increasing `dt` with the decodes). `[[Smith.block_exists]]`: for every `k`
at which the run of `tm` is defined there is a block meeting the specification, with
`n = T4 + 3`, `r = T4 + 1`, `w = H + b + n + 3f + 6`.

### The block on the System 3 side

`Rep3` of chapter 06 takes a left end that is either the finite `0^m 2 2 1^t` or
arbitrary junk guarded by `[[Smith.SafeC]]`, and a right closing that is either the
closing 1 or a 0 followed by arbitrary cells (`[[Smith.Closing]]`). The System 3
configuration at the entry of a block is `[[Smith.entry3]] L bd Rc`: the head on a 0 in
state A with a 0 to its left (whatever `L` lies beyond is never read), the block's cells
`[[Smith.BlockData.cells]]` (the rendering of chapter 06 followed by the closing 0) and
the rest `Rc` of the tape to its right. `[[Smith.blockAC_OK]]` discharges the side
conditions of `Rep3` at the entry; `[[Smith.rep3_entry]]` is the relation itself.

`[[Smith.block_sys3]]` runs `sys4_sys3_forwardSim` (chapter 06) over the block with fuel
`H + b`: at the decoding times `rep3_decode` (chapter 08) reads the doubled cyclic tag
word off the System 3 tape (through the relabelings and `toBi`), and at time `H` the
relation forces the exit shape (`[[Smith.rep3_exit_zero]]`): the System 3 head on the
closing 0 in state A with a 0 to its left. That is `entry3 L' bd' Rc'` for the next
block: the hand-off is an identity of configurations.

### The chain and the finite prefixes

`[[Smith.segCells]] bd j n` is the cells of blocks `j, ..., j + n - 1`;
`[[Smith.chain_sys3]]` composes the blocks entry to entry. `[[Smith.start3]] bd k` is the
System 3 start `([], 2, 0 :: cells of blocks 0..k, B)`: its first step `B20 -> A00>` is
the entry of block 0 with `L = []`. `[[Smith.stage_w23]]` relabels through
`sys3_sys0_forwardSim` and `toBi_run` (chapter 07): from `[[Smith.startFin]] bd k`, the
wolfram23 configuration `(B, [], 2, 0 :: cells)`, the run decodes at strictly increasing
times to the first `kk k` configurations of the machine and keeps the size of its
explicit tape throughout.

### The infinite tape

`[[Smith.tape]] bd` is the stream: a 0, then the cells of all the blocks in order (cell
`i + 1` is read off the first `i + 1` blocks, which have at least `i + 1` cells).
`[[Smith.startFin_agree]]`: `startFin bd k` agrees with `istart (tape bd)` on the state,
the left tape, the head and the explicit cells (`[[Smith.Agree]]`). `[[Smith.agree_run]]`: a
finite run that keeps its size is matched step for step by the infinite one, because
the only way a finite step differs from the infinite step is by reading the blank right
of the finite tape, which grows the size. `[[Smith.decodeTM_trunc]]`: the decoder reads
only up to the first 0 right of the head (`decodeW23_append`), so on a window that
contains the finite right tape it returns what it returns on the finite configuration;
the window `W = biSize (startFin bd k)` does. `[[Smith.stage_infinite]]` assembles the
emulation of `k` steps on the infinite tape, with "no left move from an empty left
tape" before the end of its schedule, which follows from the size invariant: a left
move from `left = []` reads the implicit blank and grows the size by one. Since the
schedule of block `k` ends after time `k` (each block takes at least one System 3
step), the clause holds at every time.

### Halting machines

Block `k` emulates the longest run of at most `k` steps: `m k` is `Nat.findGreatest` of
"step `i` exists" below `k`, and `block_exists` is applied to `m k`. For a machine that
halts at step `m`, every block from `m` on reproduces the whole run; for one that does
not halt, `m k = k`. This is why the theorem needs no hypothesis on halting, where
chapter 09's finite form needs the run to last the budget.

## Tests

`Tests/InfiniteVectors.lean` (E1-E8, all by kernel `decide`). E1-E5: D9's program
`{0, 2} * {}` in a block with `n = 7`, `r = 5`, width `2^5`, band 4. E1: the System 4
entry in 10 steps to `padCfg 7 5 0`, the exit at 13 as the padded exit configuration,
stuck alone at 14, `SafeC`. E2: the System 3 run from `entry3`, the decode at 160
(`[false]`, as D9), the exit at 224 in the shape of `rep3_exit_zero`. E3: two blocks
chained through `start3`, decodes at 161 and 385, exits at 225 and 449. E4: wolfram23
from `startFin`, decodes at 335 and 793, the exit at 917 on the last cell in state A,
size 450 kept through 917 steps and 451 at 918, the head on the first cell only at time
0. E5: `tape` at the block boundaries, `truncI 449 (istart (tape bd)) = startFin bd 1`,
the infinite run decoding on a window of 64 cells and on the theorem's window 450 at
335 and 793 and entering block 2 at 918, where the finite run leaves its tape. E6: the
program `{0} {0, 1} * {2}`, which turns once at its left end, in a block with `n = 12`,
`r = 10`, width `2^6`: the turn as `pad_turn` states it (the program's configuration
padded with no turn at block time 24, with one turn `2 * 0 + 4` steps later, the
innermost guard `{10}` merged as `{9}`), the exit at 31 as `padCfg 12 10 1`, the
System 3 exit after 1218 steps, the head never back on the leftmost cell. E7: two
blocks of different widths (`2^5` then `2^6`): `segCells`, `tape` at the boundaries,
the decodes at 335 (width 32) and 1113 (width 64), the exit at 1365 and the entry into
block 2. E8: the machine-independent side conditions of `BlockSpec` on the E1 block,
the System 4 decode at `dt 0`, the halting reading of the block index
(`Nat.findGreatest` on the one-step machine `tmH` of `Tests/TMToCTSVectors.lean`) and
the theorem instantiated on `tmH`.

## What remains existential

- The tape is existential in the statement and, in the proof, block `k` is sized from
  the run lengths of the emulation of `k` steps (`T4`, `b`, `H`, `f` from the schedules of
  chapters 04, 05 and 08), as in chapter 08. One tape per `(tm, c)` removes the
  dependence on the budget, but the size of block `k` is not given by a closed form, and
  the tape's definition uses the schedules classically (`choose`).
- The statement does not bound the work done by the encoder, and this is the objection
  that remains (chapter 09, chapter 11 item 1). The conclusion template of the theorem
  is satisfied by machines that do nothing: an infinite tape can hold, for every `k`,
  the `k + 1` configurations of the run laid out in advance, and a machine that only
  moves right over it meets every clause; and since the statement is
  `forall tm c, exists t`, the same block machinery would even give one dovetailed
  tape for all machines and inputs. What distinguishes wolfram23 is the construction
  behind the proof (Smith's encoders, whose blocks are built from the machine's
  description and the run's bookkeeping, not from the run's configurations), not the
  statement. A closed-form construction with a size bound (item 1) is what would put
  that into the statement; it is the other half of Smith's p. 22-26.
- The times are existential, one schedule per block; there is no single schedule
  across blocks (each block starts the emulation over).
- Smith starts "with the leftmost 0 active in state A"; here the start is a 2 in state
  B whose first step `B2 -> 0, R, A` puts the head on the leading 0 of block 0 in state A
  with a 0 to its left, the shape the block relation needs. This is one extra cell and
  one extra step.

## Depends on

`Smith.Guards`, `Smith.Conjecture3` with `LeftEnd.junk` and `Closing.zero` (chapter 06),
`Smith.Conjecture0` (`rep3_decode`, `rep3_exit`, `system4_emulation`, chapter 08),
`Smith.Universality` (`decodeTM`, `undbl`, chapter 09), `TagSystem.TMToCTS`
(`tm_tag_forwardSim`, `decodeCTS_word`, `step_valid`, chapter 03).
