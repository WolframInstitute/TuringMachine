# 08. T4: Smith's Conjecture 0 in finite form

## Orientation

`Smith/Conjecture0.lean` composes chapters 04 to 07 into `[[Smith.conjecture0_finite]]`:
for a two-colour cyclic tag system, an initial word and a budget, there is a finite
wolfram23 tape from which the run reproduces the working strings of the cyclic tag run
at strictly increasing times, read by the decoder `[[Smith.decodeW23]]`, stays on the
tape until then, and afterwards steps onto the cell right of the tape, a 0, in state A.
This is Smith's Conjecture 0 (TM23Proof.pdf p. 4) "for an arbitrary number of steps",
with two corrections recorded below.

## The statement

```lean
theorem conjecture0_finite (C0 : CTS) (cfg : CTSConfig) (N : Nat) (c' : CTSConfig)
    (hrun : C0.nSteps cfg (C0.appendants.length * N) = some c') (hne : c'.data ≠ []) :
    ∃ (start : BiTM.Config) (w b : Nat) (times : Nat → Nat) (T : Nat),
      IsValidWolfram23Cfg start ∧ start.state = 1 ∧
      (∀ i, i < C0.appendants.length * N → times i < times (i + 1)) ∧
      (∀ i, i ≤ C0.appendants.length * N → times i ≤ T ∧
        ∃ ci cfgi, C0.nSteps cfg i = some ci ∧ BiTM.nSteps wolfram23 start (times i) = some cfgi ∧
          decodeW23 (2 ^ w) b cfgi = some (dbl ci.data)) ∧
      (∀ τ, τ ≤ T → ∃ cfgτ, BiTM.nSteps wolfram23 start τ = some cfgτ ∧ biSize cfgτ = biSize start) ∧
      (∃ L : List Nat, BiTM.nSteps wolfram23 start (T + 1) = some ⟨1, L, 0, []⟩ ∧
        L.length = biSize start)
```

The budget is `N` cycles of the appendants; the cyclic tag run must last the
`appendants.length * N` steps of the budget and leave a nonempty word (`hne`). The
decoder returns the doubled working string `dbl ci.data` (chapter 04); chapter 09
undoubles it.

## The pieces

- `[[Smith.Bound5]]`: the integers of a System 5 configuration grow by at most one per
  step (`[[Smith.Bound5_nSteps]]`; `[[Smith.xorMerge_mem_or]]` for the pop). This bounds
  the terminal decrements and the band.
- `[[Smith.conjecture5_finite_exact]]` (chapter 04) gives an empty rule list at the end of
  the budget, the terminal event T2's exit needs.
- `[[Smith.repS4_terminal]]`: with the rules exhausted, System 4 decrements
  (`[[Smith.repS4_dStep]]`) until 1 is in the bag, then exits in state C
  (`[[Smith.repS4_exit]]`), by induction on a bound of a bag element.
- `[[Smith.RepS4_decode_band]]`: the decoder of chapter 05 below a fixed band that lies
  under the debris (`b + 2j + 2 <= 2f`) and holds every bag position (`2e - 2 < b`).
- `[[Smith.system5ToSystem4_wellFormed]]`, `[[Smith.system5ToSystem4_last_set]]`,
  `[[Smith.system5ToSystem4_elem_lt]]`: what `[[Smith.rep3_init]]` needs of the encoder
  tape (no adjacent stars; every set integer below `3f + 3`).
- `[[Smith.rep3_exit]]`: at System 4's exit configuration the relation of chapter 06
  forces the `off` focus, so the System 3 head is on the closing 1 in state C;
  `[[Smith.wolfram23_exit_step]]`: after the relabelings the wolfram23 step is
  `B2 -> 0RA` onto the implicit blank. This is Smith's exit condition, and it holds
  because System 3's rule `C10 -> A00>` reads the implicit 0 as its right neighbour.

## The decoder

```lean
def decodeW23 (N b : Nat) (cfg : BiTM.Config) : Option (List Bool) :=
  (decodeBlocks N b (cfg.head :: cfg.right.takeWhile (fun c => c != 0))).bind decodeBag
```

The head cell and the cells right of it up to the first 0 are the blocks of the leading
conglomerate (the star after the leading sets is a 0 standing in for the first cell of
the next set, so the run of nonzero cells is exactly `|K| * N` long).
`[[Smith.decodeBlocks]]` checks that they are 1s and 2s making whole blocks, XORs the
blocks (`[[Smith.xorBlocks]]`), takes the parity set of the XOR below `b`
(`[[Smith.parAt]]`, `[[Smith.parAt_blocks]]`), and reads it as chapter 05 does (`x / 2 + 1`
on an even set, `none` otherwise); `[[Smith.decodeBag]]` then reads the working string.

`[[Smith.rep3_decode]]`: at a System 4 configuration with the head on an element in
state B that leads a block of sets followed by a star, the configuration one step after
every scheduled time of T2, `decodeW23` agrees with `decodeS4`; the cells left of the
head play no part. The decoding times are therefore the T2 times plus one System 4 step,
carried to System 0 by the T3 schedule.

## The parameter choices, and what they mean

The proof composes the finite forms by their schedules rather than by `ForwardSim_comp`,
because the fuel lives in a different source system at each link. The parameters are
picked in order, each from quantities the earlier schedules produced:

| parameter | choice | why |
|---|---|---|
| `t5` | the System 5 schedule of T1 exact | `t5 n` is the System 5 run length for the whole budget |
| `B0` | a bound on the integers of the System 5 program | `Bound5`, from `exists_int_bound` |
| `M` | `(B0 + t5 n).toNat` | some bag element is at most `M + 1` at the end, so at most `M` terminal decrements |
| `H` | `t5 n + M + 1` | T2's budget: the run plus the terminal phase |
| `f` | `B0.toNat + 2H + 2 t5 n + 5` | T2's bounds `e < f`, `k + 2H < f`, `2H < f` |
| `b` | `2f - 2 t5 n - 2` | the band lies under the debris for every `j <= t5 n` and above every bag position |
| `t4`, `k`, `T4` | T2's schedule, the terminal count, `T4 = t4 (t5 n) + k` | the System 4 exit time |
| `h4` | `T4 + b` | T3's fuel must cover the System 4 run and the band |
| `w` | `h4 + 3f + 6` | `2^w > w` covers `h4 + 3 <= 2^w` and `3f + 3 <= 2^w` (every set element below the width) |

Every parameter therefore depends on the run lengths `t5 n`, `T4` and `k` of the
emulation itself. The tape `start` exhibited by the proof is sized by running Systems 5
and 4, which are themselves emulating the machine. This is the Pratt-style objection to
Smith's proof, instantiated rather than answered: Smith computes `f` and `w` from an a
priori bound on the System 5 finish time (`3^(n-1) M`, p. 20-21) and argues on p. 22-26
that the initial condition can be produced by an obviously non-universal algorithm.
Closing this gap needs (i) the finish-time bound for T2, (ii) a System 4 exit-time bound
(the step counts of the D-step and P-step lemmas are explicit, so this is bookkeeping),
(iii) a bound on the tag steps of chapter 03 in terms of the tape length and the number
of machine steps, and (iv) a definition `IC` of the tape from those bounds with the
theorem restated as `start = IC ...` or with `biSize start <= F ...` for a closed form
`F`. Chapter 11 lists this as the main open item.

## Corrections to Smith's statement

- The head does not start on the leftmost cell of the tape but on the first cell of the
  first block, as in Smith's `s42s0-3.pl` output; the leftmost cell is a 0, as the
  conjecture says, but the tape started on it in state A walks off its left end in
  three steps (chapter 06). `docs/PLAN.md` section 2 T4 still says "started on its
  leftmost cell in state A" and must be corrected (chapter 11).
- The run must be assumed to last the budget without emptying the word: an emptied word
  empties the System 5 bag, System 4 then sweeps forever and never exits.

## Notes and caveats

- "Never visits a cell outside the tape" is `biSize` constant, since a wolfram23 step
  onto an implicit blank grows the explicit tape and the zipper run is defined
  (`[[Smith.lnSteps_length]]`, `[[Smith.toBi_run]]`).
- The times `times` and `T` are existential, with no closed form and no event in the
  wolfram23 run that marks them. Nothing is stated about `decodeW23` at other times; on
  the D9 test tape it returns `some` at several unscheduled times as well.
- The D9 vectors of `Tests/SmithVectors.lean` exercise `decodeW23` on System 3 tapes
  built by `initAC`, with negative instances (a state-A head, an odd parity position, a
  tape without whole blocks). No vector runs `conjecture0_finite` end to end; with
  `w = h4 + 3f + 6` the block width of the smallest instance is far beyond `decide`.

## Depends on

`Smith.Conjecture0`, and chapters 04 to 07.
