/-
  Tests.TMToCTSVectors

  Regression vectors for T7 (milestone M4b): a three-state binary machine
  run through the Cocke-Minsky tag system and the cyclic tag system, and
  read back by the decoder.

  `tmEx` in state 1 on `0` writes `1`, moves right into state 2; on `1`
  writes `0`, moves left, stays; in state 2 on `0` writes `1`, moves left
  into state 1; on `1` writes `1`, moves right, stays. From `1, [], 0, [1, 1]`
  it makes three moves to the right and one to the left. The tag step counts
  are the round lengths of `TagSystem.CockeMinsky`: `(m + N + 2) + 2 (m +
  N/2 + 2)` for a move to the right, five rounds for a move to the left.
  Through Cook's cyclic tag system one tag step is `2 * 253` steps (the
  alphabet has `1 + 84 * 3` symbols). The decoder drops trailing blanks and
  rejects a word that is not an encoding.
-/

import TagSystem.TMToCTS

namespace Tests

open TagSystem
open TM
open BiTM

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
  native_decide

/-- The decoder reads the configurations back, without trailing blanks. -/
example : decodeCTS 3 (ctsOfCfg 3 ⟨2, [1, 1, 1], 0, []⟩) = some ⟨2, [1, 1, 1], 0, []⟩ := by
  native_decide
example : decodeCTS 3 (ctsOfCfg 3 ⟨2, [1, 0], 0, [1, 0]⟩) = some ⟨2, [1], 0, [1]⟩ := by
  native_decide
example : decodeCTS 3 ⟨[true, false], 0⟩ = none := by native_decide

end Tests
