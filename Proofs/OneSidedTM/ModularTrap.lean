/-
  OneSidedTM.ModularTrap

  A parametric family of "near-miss" TMs that compute binary successor
  correctly for MOST inputs but fail at specific carry depths.

  The (p+1)-state TM uses p states to count carry propagation depth
  modulo p. State p's absorb transition writes 0 instead of 1 (bug).

  For p = 10 (11 states): passes all n ∈ [1, 510], fails at n = 511.

  The construction scales exponentially:
  - p = 52 (53 states): first failure at n = 2^51 - 1 ≈ 2.25 × 10^15
  - p = 100 (101 states): first failure at n = 2^99 - 1 ≈ 6.3 × 10^29

  This demonstrates "leverage of raw compute": O(p) states requires
  O(2^p) brute-force tests to find the failure, but O(p) lines of proof.
-/

import OneSidedTM.Basic

namespace OneSidedTM
open TM

-- ============================================================================
-- The Modular Trap TM (p = 10, 11 states)
-- ============================================================================

/-- The modular trap TM with p=10.
    States 1..10: carry counter states (count carry depth mod 10).
    State 11: walk-back state.
    Bug: state 10 on symbol 0 writes 0 instead of 1. -/
def modTrap10 : TM := {
  numStates := 11
  numSymbols := 2
  transition := fun state sym =>
    match state, sym with
    -- Carry: flip 1→0, move L toward MSB, advance state counter
    | 1, 1 => { nextState := 2,  write := 0, dir := Dir.L }
    | 2, 1 => { nextState := 3,  write := 0, dir := Dir.L }
    | 3, 1 => { nextState := 4,  write := 0, dir := Dir.L }
    | 4, 1 => { nextState := 5,  write := 0, dir := Dir.L }
    | 5, 1 => { nextState := 6,  write := 0, dir := Dir.L }
    | 6, 1 => { nextState := 7,  write := 0, dir := Dir.L }
    | 7, 1 => { nextState := 8,  write := 0, dir := Dir.L }
    | 8, 1 => { nextState := 9,  write := 0, dir := Dir.L }
    | 9, 1 => { nextState := 10, write := 0, dir := Dir.L }
    | 10, 1 => { nextState := 1, write := 0, dir := Dir.L }
    -- Absorb: hit a 0 during carry → write 1, move R, enter walk-back
    | 1, 0 => { nextState := 11, write := 1, dir := Dir.R }
    | 2, 0 => { nextState := 11, write := 1, dir := Dir.R }
    | 3, 0 => { nextState := 11, write := 1, dir := Dir.R }
    | 4, 0 => { nextState := 11, write := 1, dir := Dir.R }
    | 5, 0 => { nextState := 11, write := 1, dir := Dir.R }
    | 6, 0 => { nextState := 11, write := 1, dir := Dir.R }
    | 7, 0 => { nextState := 11, write := 1, dir := Dir.R }
    | 8, 0 => { nextState := 11, write := 1, dir := Dir.R }
    | 9, 0 => { nextState := 11, write := 1, dir := Dir.R }
    -- === BUG === : state 10 writes 0 instead of 1
    | 10, 0 => { nextState := 11, write := 0, dir := Dir.R }
    -- Walk-back: preserve tape, move R until halt at position 0
    | 11, 0 => { nextState := 11, write := 0, dir := Dir.R }
    | 11, 1 => { nextState := 11, write := 1, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.R }
}

-- ============================================================================
-- Verification helper
-- ============================================================================

private def checkModTrap (n : Nat) (fuel : Nat) : Bool :=
  match run modTrap10 n fuel with
  | some v => v == n + 1
  | none => false

-- ============================================================================
-- Part 1: Correct on 1..510 (bulk verification via native_decide)
-- ============================================================================

/-- The modular trap TM computes n+1 for all inputs 1..510.
    This requires 510 cases, each verified by computation. -/
theorem modTrap10_correct_1_to_510 :
    ∀ n : Fin 511, n.val ≥ 1 → checkModTrap n.val 5200 = true := by
  native_decide

-- ============================================================================
-- Part 2: Failure at n = 511
-- ============================================================================

/-- The modular trap TM does NOT produce 512 at input 511.
    Input 511 = 111111111 (9 trailing 1-bits, carry depth 9 ≡ 9 mod 10).
    After 9 carries, state = 10 (the bug state).
    State 10 absorbs with write=0, producing output 0. -/
theorem modTrap10_fails_at_511 :
    checkModTrap 511 5200 = false := by native_decide

/-- The exact output: the TM produces 0 at input 511 -/
theorem modTrap10_511_gives_0 :
    run modTrap10 511 5200 = some 0 := by native_decide

-- ============================================================================
-- Part 3: Not a successor machine
-- ============================================================================

/-- The modular trap TM is NOT a successor machine.
    It passes all inputs 1..510 but fails at 511.
    This is a near-miss with depth 510 — the deepest we've seen. -/
theorem modTrap10_not_successor :
    ¬ (∀ n : Nat, n ≥ 1 → ∃ fuel cfg, eval modTrap10 (initConfig n) fuel = some cfg ∧
       fromBinary (trimTrailingZeros cfg.tape) = n + 1) := by
  intro h
  obtain ⟨fuel, cfg, heval, hval⟩ := h 511 (by omega)
  have hdet := eval_det modTrap10 (initConfig 511) fuel 20 cfg
    ⟨11, 0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ heval (by native_decide)
  subst hdet
  simp [fromBinary, trimTrailingZeros] at hval

-- ============================================================================
-- Part 4: The general theorem (documented, not formalized)
-- ============================================================================

/-!
## Exponential Scaling Theorem

For any p ≥ 3, the (p+1)-state modular trap TM satisfies:

1. **Correctness:** For all n ∈ [1, 2^(p-1) - 2], the TM outputs n + 1.
2. **Failure:** At n = 2^(p-1) - 1, the TM outputs 0.
3. **Mechanism:** The carry depth of n = 2^(p-1) - 1 is exactly p - 1.
   After p - 1 carries, the state counter reaches state p.
   State p's absorb transition writes 0 (the bug), not 1.
4. **Scaling:** With O(p) states, one needs O(2^p) brute-force tests
   to discover the failure, but only O(p) lines of mathematical proof.

### Key Insight: Why Non-Successor Functions Aren't Needed

This construction shows that deep near-misses ARE possible for successor,
but only with MORE STATES. The (3,2) and (4,2) spaces are too small
because the carry counter can only reach depth 2 or 3 before cycling.
With p+1 states, the counter reaches depth p-1 before cycling.

The "leverage of raw compute" comes from the exponential gap between
the state count and the failure point: O(p) states vs O(2^p) test inputs.

### Examples

| p | States | First failure | Tests needed |
|---|--------|--------------|-------------|
| 10 | 11 | 511 | 510 |
| 20 | 21 | 524,287 | ~500K |
| 50 | 51 | 2^49 - 1 | ~562 trillion |
| 100 | 101 | 2^99 - 1 | ~6.3 × 10^29 |
-/

end OneSidedTM
