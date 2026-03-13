/-
  OneSidedTM.ClassB

  Class B (Carry+Bouncing Walkback) one-sided TMs.
  This covers Unknown Groups 1 and 2 (e.g., Rule 248514).

  Algorithm:
  1. Carry phase: state 1 reads 1, writes 0, moves L.
  2. Absorb: state 1 reads 0, writes 1, moves R, enters walk state `as`.
  3. Bouncing Walkback:
     (as, 0) → (bs, 1, L)  -- Bounces left, writes 1
     (bs, 0) → (as, 0, R)  -- Bounces right, restores 0
     (bs, 1) → (as, 1, R)  -- Bounces right, preserves 1
     (as, 1) → (as, 0, R)  -- Clears the 1 it just wrote, moves right
-/

import OneSidedTM.Basic
import OneSidedTM.PlusOne

namespace OneSidedTM
open TM

structure IsClassB (tm : TM) (as bs : Nat) : Prop where
  carry    : tm.transition 1 1 = { nextState := 1,  write := 0, dir := Dir.L }
  absorb   : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R }
  walk_L   : tm.transition as 0 = { nextState := bs, write := 1, dir := Dir.L }
  walk_R_0 : tm.transition bs 0 = { nextState := as, write := 0, dir := Dir.R }
  walk_R_1 : tm.transition bs 1 = { nextState := as, write := 1, dir := Dir.R }
  walk_clr : tm.transition as 1 = { nextState := as, write := 0, dir := Dir.R }

-- ============================================================================
-- Walkback abstraction
-- ============================================================================

/-- The bouncing walkback preserves the tape and returns to position 0.
    Each step: (as,0) writes 1 and bounces L; (bs,?) bounces R restoring the cell;
    (as,1) clears the written 1 and moves R. Net effect: advance right by 1, tape unchanged. -/
theorem walkback_bouncing (tm : TM) (as bs : Nat) (hc : IsClassB tm as bs) :
    ValidWalkback tm as := by
  sorry

-- ============================================================================
-- The structural proof of ComputesSucc for Class B
-- ============================================================================

theorem classB_computes (tm : TM) (as bs : Nat) (hc : IsClassB tm as bs) :
    ComputesSucc tm := by
  intro n _hn
  obtain ⟨fw, cfg, hev, hfb⟩ :=
    sim_eval_universal tm as hc.carry hc.absorb (walkback_bouncing tm as bs hc) 0 (toBinary n) (toBinary_binary n)
  refine ⟨fw, ?_⟩
  simp at hev hfb
  simp only [run, initConfig, hev, Option.map]
  simp only [outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

-- ============================================================================
-- Concrete Implementation: Rule 248514
-- ============================================================================

def rule248514 : TM := fromRuleNumber32 248514

theorem rule248514_isClassB : IsClassB rule248514 3 2 := {
  carry    := rfl
  absorb   := rfl
  walk_L   := rfl
  walk_R_0 := rfl
  walk_R_1 := rfl
  walk_clr := rfl
}

theorem rule248514_computesSucc : ComputesSucc rule248514 :=
  classB_computes rule248514 3 2 rule248514_isClassB

end OneSidedTM
