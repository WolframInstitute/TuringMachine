/-
  OneSidedTM.NearMiss

  Rule 156830 (3-state, 2-symbol) computes binary successor for inputs 1..6
  but fails at input 7: it outputs 9 instead of 8.

  This is a carry-propagation failure: the machine handles carries through
  ≤2 consecutive 1-bits but fails when 3+ consecutive 1-bits need carrying.
-/

import OneSidedTM.Basic

namespace OneSidedTM
open TM

/-- Rule 156830: the near-miss 3-state TM -/
def nearMiss : TM := {
  numStates := 3
  numSymbols := 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 2, 0 => { nextState := 3, write := 0, dir := Dir.R }
    | 2, 1 => { nextState := 2, write := 1, dir := Dir.L }
    | 3, 0 => { nextState := 1, write := 0, dir := Dir.R }
    | 3, 1 => { nextState := 2, write := 0, dir := Dir.L }
    | _, _ => { nextState := 1, write := 0, dir := Dir.R }
}

/-- Helper: check a single run -/
private def checkNearMiss (n : Nat) (fuel : Nat) : Bool :=
  match eval nearMiss (initConfig n) fuel with
  | some cfg => fromBinary (trimTrailingZeros cfg.tape) == n + 1
  | none => false

/-- The near-miss rule correctly computes n+1 for all inputs 1 through 6 -/
theorem nearMiss_correct_1_to_6 :
    checkNearMiss 1 10 ∧ checkNearMiss 2 10 ∧ checkNearMiss 3 10 ∧
    checkNearMiss 4 10 ∧ checkNearMiss 5 10 ∧ checkNearMiss 6 10 := by native_decide

/-- Rule 156830 does NOT compute the successor function.
    At input 7 (binary 111), it halts with output 9 instead of 8.
    Proof: eval_det gives uniqueness of the halted config,
    and native_decide verifies the config has wrong output value. -/
theorem nearMiss_not_successor :
    ¬ (∀ n, ∃ fuel cfg, eval nearMiss (initConfig n) fuel = some cfg ∧
       fromBinary cfg.tape = n + 1) := by
  intro h
  obtain ⟨fuel, cfg, heval, hval⟩ := h 7
  have hdet := eval_det nearMiss (initConfig 7) fuel 10 cfg
    ⟨2, 0, [1, 0, 0, 1]⟩ heval (by native_decide)
  subst hdet
  simp [fromBinary] at hval

/-- The failure also manifests at input 15 (binary 1111):
    same carry-propagation bug at longer runs of 1s. -/
theorem nearMiss_fails_at_15 :
    ¬ checkNearMiss 15 100 = true := by native_decide

end OneSidedTM
