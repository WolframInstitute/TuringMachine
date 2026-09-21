# 09. T8: the composition

## Orientation

`Smith/Universality.lean` composes T7 (chapter 03) with T4 (chapter 08) into
`[[Smith.wolfram23_universal]]`, quoted in full in chapter 01. This chapter records how
the composition is made, what the decoder is, and which of the referee's objections the
statement answers and which it does not.

## The decoder

```lean
def undbl : List Bool → Option (List Bool)
  | [] => some []
  | [_] => none
  | a :: b :: rest => if a = b then (undbl rest).map (a :: ·) else none

def decodeTM (S N b : Nat) (cfg : BiTM.Config) : Option Config :=
  (decodeW23 N b cfg).bind fun d => (undbl d).bind fun data => decodeCTS S ⟨data, 0⟩
```

`[[Smith.undbl]]` inverts `dbl` on doubled words and returns `none` elsewhere
(`[[Smith.undbl_dbl]]`). `[[Smith.decodeTM]] S N b` reads the doubled cyclic tag word off
the wolfram23 tape (`decodeW23`, chapter 08), undoubles it, and reads the machine
configuration off the cyclic tag word (`decodeCTS`, chapter 03), up to trailing blanks.
It is a fixed function of `(S, N, b)` and of the cells from the head up to the first 0
to its right; it does not see the machine, the input or the run.

## The composition

The cyclic tag system of T7 makes exactly one cycle of its `2 (1 + 84 S)` appendants
per tag step (`[[TagSystem.cts_of_tag]]`, `[[TagSystem.tagToCTS_appendants_length]]`).
So T4 is applied with the budget of `tt n` cycles, where `tt` is the tag-level schedule
of `[[TagSystem.tm_tag_forwardSim]]` for the machine's `n` steps: the cyclic tag run of
`2 (1 + 84 S) tt n` steps is the one T4 requires, and its last word is the encoding of
the last configuration word, nonempty because a configuration word has at least four
symbols (`[[TagSystem.length_word]]`). At cyclic tag time `2 (1 + 84 S) tt i` the cyclic
tag configuration is `ctsOfCfg S c_i`, and the decoders compose: `decodeW23` returns
`dbl` of its data, `undbl` returns the data, `decodeCTS` returns `canon c_i`
(`[[TagSystem.decodeCTS_word]]`). The confinement and exit clauses are those of
`conjecture0_finite`, unchanged.

## What the statement answers, and what it leaves open

Answered by the statement as it stands:

- The decoder is fixed and position-relative, and it is a left inverse of the encoders
  only at the scheduled times by the theorem; it is not a table lookup into `tm` or `c`.
- The times are strictly increasing, the machine configurations are those of the given
  run (`BiTM.nSteps tm c i = some ci`), and confinement and exit are stated and proved.
- No axiom beyond `propext`, `Classical.choice`, `Quot.sound`; no `sorry`; no
  `native_decide` in the cone.

Left open by the statement (the independent review of 2026-09-21; chapter 11):

- One tape per machine, configuration and budget `n`, with the tape sized in the proof
  from the run lengths of the emulating systems (chapter 08). The standard notion of
  universality asks for one encoding of `(M, x)` independent of the running time. The
  conclusion template is satisfied by a machine that only moves right over a tape on
  which the `n + 1` configurations have been laid out in advance; what distinguishes
  wolfram23 is the proof term (Smith's encoders), not the statement. Two remedies: the
  infinite form (chapter 10, proved: `[[Smith.wolfram23_infinite]]`), one right-infinite
  tape per `(M, x)` with the whole run decodable; and a closed-form initial condition
  with a size bound (chapter 11, open).
- Binary machines only.
- Decoding up to `canon`, at existential times, with nothing said about other times.
- The name `wolfram23_universal` and the M8 notes' "universality in the literal sense"
  claim more than the statement; the docstring at lines 48-56 of the module states the
  `n`-step form correctly.

## Notes and caveats

- No regression vector runs `decodeTM` on encoder output: with the proof's `w` the block
  width is far beyond `decide`. `undbl` is covered by `undbl_dbl`, `decodeW23` by the D9
  vectors, `decodeCTS` by `Tests/TMToCTSVectors.lean`; on the D9 positive tape
  `decodeTM` returns `none` because the doubled word there has odd length. A
  hand-picked small instance for `decodeTM` should be added (chapter 11).
- `docs/PLAN.md` M8 row names the type `BiTM.Machine`; the type is `TM.Machine`
  (chapter 11).

## Depends on

`Smith.Universality`, chapters 03 and 08.
