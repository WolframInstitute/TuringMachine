/-
  Vectors.ClosedFormVectors

  Regression vectors for the closed-form initial condition (milestone M9,
  open item 1): the run bounds of `Smith.RunBounds` and `TagSystem.TagBounds`
  against the exact run lengths on small instances, and the closed-form
  parameters of `Smith.ClosedForm` on the program of D4.

  F1: the System 5 programs of D1 (`ctsToSystem5 ctsD1 cfgD1 1`) and D4
  (`s5D4`) of `Vectors.SmithVectors` run 10 and 11 steps; the bound
  `icT5 = maxInt5 * 2 ^ (number of rules)` is 7168 and 96. F2: the System 4
  tape of D4 at `f = 16` (545 elements) runs 9906 steps, below the bound
  `(2 L + 2) (L + 1) = 596232`. F3: the closed-form parameters of D4 (`icF`,
  `icBand`, and `icT4`, `icW` from the tape length), computed without
  running anything (the tape length itself is too long for the kernel).
  F4: the raw run of `tmH` of `Vectors.TMToCTSVectors` goes on
  after the machine halts (the halting row read as an ordinary one), agrees
  with the run while it is defined, and its tag times are below
  `n * 15 * 2 ^ (sz c + n)`; the same for `tmEx`. F5: the budget of
  `IC tmH c 1`.

  Everything closes by `decide +kernel` (kernel reduction, no extra axiom)
  or `decide`; nothing outside this file depends on it. The initial
  conditions themselves (`IC`, `ITape`) are far too large to evaluate: the
  System 5 program of `IC tmH c 1` already has 40560 rules (by `#eval`).
-/

import Vectors.SmithVectors
import Vectors.TMToCTSVectors
import Smith.Infinite

namespace Tests

open Smith
open BiTM
open TM
open TagSystem

/-! ## F1: the System 5 bound -/

example : maxInt5 (ctsToSystem5 ctsD1 cfgD1 1) = 28 ∧
    (ctsToSystem5 ctsD1 cfgD1 1).rules.length = 8 ∧ icT5 (ctsToSystem5 ctsD1 cfgD1 1) = 7168 := by
  decide +kernel

example : maxInt5 s5D4 = 6 ∧ icT5 s5D4 = 96 := by decide +kernel

/-- D4's System 5 run lasts 11 steps. -/
example : (System5.nSteps s5D4 11).isSome = true ∧ System5.nSteps s5D4 12 = none := by
  decide +kernel

/-! ## F2: the System 4 bound -/

example : s4D4.elems.length = 545 ∧
    (2 * s4D4.elems.length + 2) * (s4D4.elems.length + 1) = 596232 := by decide +kernel

/-! ## F3: the closed-form parameters of D4 -/

example : icF s5D4 = 601 ∧ icBand s5D4 = 1008 := by decide +kernel

/-- The System 4 tape at `icF s5D4` has `1 + 2 * 601 + 4 * 8 * 601 = 20435`
    elements (one bag set, 601 star/empty pairs, `8 f` elements per rule), too
    many to count in the kernel; from that length on the parameters are
    arithmetic. -/
example : (2 * 20435 + 2) * (20435 + 1) = 835260192 ∧
    Nat.size (835260192 + icBand s5D4 + 3 * icF s5D4 + 6) = 30 := by decide +kernel

/-! ## F4: the raw run and the tag times -/

/-- `tmH` halts after one step; the raw run reads the halting row as an
    ordinary one and keeps moving right on blanks. -/
example : rawRun tmH ⟨1, [], 0, []⟩ 1 = ⟨0, [1], 0, []⟩ ∧
    rawRun tmH ⟨1, [], 0, []⟩ 3 = ⟨0, [0, 0, 1], 0, []⟩ := by decide

/-- The tag times: 6 tag steps for the first move (three rounds of two, as
    in `Vectors.TMToCTSVectors`), then the bound `n * 15 * 2 ^ (sz c + n)`. -/
example : (List.range 5).map (tagTime tmH ⟨1, [], 0, []⟩) = [0, 6, 15, 27, 45] := by
  decide +kernel

example : (List.range 5).all (fun n =>
    tagTime tmH ⟨1, [], 0, []⟩ n ≤ n * 15 * 2 ^ (sz (⟨1, [], 0, []⟩ : Config) + n)) = true := by
  decide +kernel

example : (List.range 5).map (tagTime tmEx ⟨1, [], 0, [1, 1]⟩) = [0, 18, 32, 48, 85] ∧
    (List.range 5).all (fun n => tagTime tmEx ⟨1, [], 0, [1, 1]⟩ n
      ≤ n * 15 * 2 ^ (sz (⟨1, [], 0, [1, 1]⟩ : Config) + n)) = true := by
  decide +kernel

/-! ## F5: the budget of `IC tmH c 1` -/

example : icN (⟨1, [], 0, []⟩ : Config) 1 = 30 := by decide

end Tests
