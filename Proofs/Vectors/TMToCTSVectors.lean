/-
  Vectors.TMToCTSVectors

  Regression vectors for T7 (milestone M4b): a three-state binary machine
  run through the Cocke-Minsky tag system and the cyclic tag system, and
  read back by the decoder; a two-state machine that halts after one step;
  the decoder on words that are not encodings; and the last two stages of
  the composite decoder `Smith.decodeTM` of T8 (`undbl`, then `decodeCTS`).

  `tmEx` in state 1 on `0` writes `1`, moves right into state 2; on `1`
  writes `0`, moves left, stays; in state 2 on `0` writes `1`, moves left
  into state 1; on `1` writes `1`, moves right, stays. From `1, [], 0, [1, 1]`
  it makes three moves to the right and one to the left. The tag step counts
  are the round lengths of `TagSystem.CockeMinsky`: `(m + N + 2) + 2 (m +
  N/2 + 2)` for a move to the right, five rounds for a move to the left.
  Through Cook's cyclic tag system one tag step is `2 * 253` steps (the
  alphabet has `1 + 84 * 3` symbols). The decoder drops trailing blanks and
  rejects a word that is not an encoding.

  `tmH` in state 1 on `0` writes `1`, moves right and halts; on `1` writes
  `1`, moves right, stays. From `1, [], 0, []` it halts after one step in
  `0, [1], 0, []`, which the tag system reaches after `2 + 2 + 2` tag steps
  (`m, N = 0, 0`) and the cyclic tag system after `2 * 169 * 6` steps.

  The decoders `symbolDecode`, `tagWordDecode`, `decodeCTS` go through
  well-founded recursions (`tagWordDecode`, `natBits`, `termination_by`),
  which `decide` cannot unfold, so their vectors and the two cyclic tag runs
  close by `decide +kernel` (kernel reduction, no extra axiom); everything
  else closes by `decide`. No `native_decide`.
-/

import TagSystem.TMToCTS
import Smith.Universality

namespace Tests

open TagSystem
open TM
open BiTM

/-! ## A three-state machine -/

def tmEx : Machine where
  numStates := 3
  numSymbols := 2
  transition := fun q s =>
    match q, s with
    | 1, 0 => ⟨2, 1, Dir.R⟩
    | 1, 1 => ⟨1, 0, Dir.L⟩
    | 2, 0 => ⟨1, 1, Dir.L⟩
    | 2, 1 => ⟨2, 1, Dir.R⟩
    | _, _ => ⟨0, 0, Dir.R⟩

example : WF tmEx := by decide

def cEx0 : Config := ⟨1, [], 0, [1, 1]⟩

example : BiTM.nSteps tmEx cEx0 4 = some ⟨1, [1, 1], 1, [1]⟩ := by decide

/-- Three moves to the right: `m + N + 2 + 2 (m + N / 2 + 2)` tag steps each
    (`m, N = 0, 6`; `1, 3`; `3, 1`). -/
example : nStepsP (prod tmEx) (word cEx0) 18 = some (word ⟨2, [1], 1, [1]⟩) := by decide
example : nStepsP (prod tmEx) (word ⟨2, [1], 1, [1]⟩) 14 = some (word ⟨2, [1, 1], 1, []⟩) := by decide
example : nStepsP (prod tmEx) (word ⟨2, [1, 1], 1, []⟩) 16 = some (word ⟨2, [1, 1, 1], 0, []⟩) := by
  decide

/-- A move to the left (`m, N = 7, 0`): five rounds, 37 tag steps. -/
example : nStepsP (prod tmEx) (word ⟨2, [1, 1, 1], 0, []⟩) 37 = some (word ⟨1, [1, 1], 1, [1]⟩) := by
  decide

/-- Not earlier. -/
example : nStepsP (prod tmEx) (word cEx0) 17 ≠ some (word ⟨2, [1], 1, [1]⟩) := by decide

/-- The same first step through the cyclic tag system. -/
example : (tagToCTS (tagK tmEx 3) (K_pos 3)).nSteps (ctsOfCfg 3 cEx0) (2 * 253 * 18)
    = some (ctsOfCfg 3 ⟨2, [1], 1, [1]⟩) := by
  decide +kernel

/-- The decoder reads the configurations back, without trailing blanks. -/
example : decodeCTS 3 (ctsOfCfg 3 ⟨2, [1, 1, 1], 0, []⟩) = some ⟨2, [1, 1, 1], 0, []⟩ := by
  decide +kernel
example : decodeCTS 3 (ctsOfCfg 3 ⟨2, [1, 0], 0, [1, 0]⟩) = some ⟨2, [1], 0, [1]⟩ := by
  decide +kernel
example : decodeCTS 3 ⟨[true, false], 0⟩ = none := by decide +kernel

/-! ## Words that are not encodings

`symbolDecode k` accepts exactly the one-hot blocks of length `k`, and
`tagWordDecode k` exactly their concatenations (`tagWordDecode_sound`): a
block of the wrong length, a short last block, or a stray bit after the last
block is rejected, however the bits are placed. -/

example : symbolDecode 5 [false, true, false, false, false] = some 1 := by decide
example : symbolDecode 5 [false, true, false, false] = none := by decide
example : symbolDecode 5 [true] = none := by decide
example : symbolDecode 5 [false, true, false, true, false] = none := by decide
example : symbolDecode 5 [false, false, false, false, false] = none := by decide

example : tagWordDecode 3 (by decide) [false, true, false, true, false, false] = some [1, 0] := by
  decide +kernel
example : tagWordDecode 3 (by decide) [false, true, false, true, false] = none := by decide +kernel
example : tagWordDecode 3 (by decide) [false, true, false, true] = none := by decide +kernel
example : tagWordDecode 3 (by decide) [] = some [] := by decide +kernel

/-- The encoding of a configuration with its last bit dropped (the last block
    short by one) or with a `true` appended (a stray block of length one)
    does not decode. -/
example : decodeCTS 3 ⟨(ctsOfCfg 3 ⟨2, [1, 1, 1], 0, []⟩).data.dropLast, 0⟩ = none := by
  decide +kernel
example : decodeCTS 3 ⟨(ctsOfCfg 3 ⟨2, [1, 1, 1], 0, []⟩).data ++ [true], 0⟩ = none := by
  decide +kernel

/-! ## A machine that halts after one step -/

def tmH : Machine where
  numStates := 2
  numSymbols := 2
  transition := fun q s =>
    match q, s with
    | 1, 0 => ⟨0, 1, Dir.R⟩
    | 1, 1 => ⟨1, 1, Dir.R⟩
    | _, _ => ⟨0, 0, Dir.R⟩

example : WF tmH := by decide

example : BiTM.nSteps tmH ⟨1, [], 0, []⟩ 1 = some ⟨0, [1], 0, []⟩ := by decide
example : BiTM.nSteps tmH ⟨1, [], 0, []⟩ 2 = none := by decide

/-- The move to the right with `m, N = 0, 0`: three rounds of two tag steps,
    and the word of the halted configuration. -/
example : nStepsP (prod tmH) (word ⟨1, [], 0, []⟩) 6 = some (word ⟨0, [1], 0, []⟩) := by decide
example : nStepsP (prod tmH) (word ⟨1, [], 0, []⟩) 5 ≠ some (word ⟨0, [1], 0, []⟩) := by decide

/-- The same step through the cyclic tag system: `2 * (1 + 84 * 2)` steps per
    tag step. -/
example : (tagToCTS (tagK tmH 2) (K_pos 2)).nSteps (ctsOfCfg 2 ⟨1, [], 0, []⟩) (2 * 169 * 6)
    = some (ctsOfCfg 2 ⟨0, [1], 0, []⟩) := by
  decide +kernel

/-- The halted configuration reads back. -/
example : decodeCTS 2 (ctsOfCfg 2 ⟨0, [1], 0, []⟩) = some ⟨0, [1], 0, []⟩ := by decide +kernel

/-! ## The last two stages of `Smith.decodeTM`

`Smith.decodeTM S N b` is `decodeW23 N b`, then `Smith.undbl`, then
`decodeCTS S`. The first stage needs a wolfram23 tape whose bag spells a
doubled cyclic tag word, at least `2 * 4 * (1 + 84 S)` bits, so a block of
width at least `2^13` for `S = 2`, whose rendering builds its parity rows by
iteration and is out of reach of `decide`; `Vectors/SmithVectors.lean` D9 and
D10 have the first stage on small tapes and `decodeTM` rejecting their
words. Here `undbl` inverts `dbl` and rejects an odd word and a word that
is not doubled, and the doubled encoding of a configuration, taken from the
definitions, comes back as the configuration. -/

example : Smith.undbl (Smith.dbl [true, false, false, true]) = some [true, false, false, true] := by
  decide
example : Smith.undbl [true, false] = none := by decide
example : Smith.undbl [true] = none := by decide
example : Smith.undbl [] = some [] := by decide

example : (Smith.undbl (Smith.dbl (ctsOfCfg 2 ⟨1, [], 0, []⟩).data)).bind
      (fun data => decodeCTS 2 ⟨data, 0⟩) = some ⟨1, [], 0, []⟩ := by
  decide +kernel

example : (Smith.undbl (Smith.dbl (ctsOfCfg 2 ⟨0, [1], 0, []⟩).data)).bind
      (fun data => decodeCTS 2 ⟨data, 0⟩) = some ⟨0, [1], 0, []⟩ := by
  decide +kernel

/-- The encoding itself is not a doubled word (`undbl` fails at the first
    one-hot `true`, which stands next to a `false`). -/
example : Smith.undbl (ctsOfCfg 2 ⟨1, [], 0, []⟩).data = none := by decide +kernel

end Tests
