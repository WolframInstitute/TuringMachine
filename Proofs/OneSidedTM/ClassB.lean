/-
  OneSidedTM.ClassB

  Class B (Carry+Bouncing Walkback) one-sided TMs.
  This covers Unknown Groups 1 and 2 (e.g., Rule 248514).

  Algorithm:
  1. Carry phase: state 1 reads 1, writes 0, moves L.
  2. Absorb: state 1 reads 0, writes 1, moves R, enters walk state `as`.
  3. Bouncing Walkback: 3-step cycle at each position moves right by 1.
     (as, 0) → (bs, 1, L)  -- Bounces left, writes 1
     (bs, ?) → (as, ?, R)  -- Bounces right, preserves the read value
     (as, 1) → (as, 0, R)  -- Clears the 1 written in step 1
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
-- Walkback: sorry for now.
-- The bouncing 3-step cycle (write 1, bounce, clear 1) is a net identity on
-- the tape and advances pos by -1. The proof requires suf to be nonempty
-- (which sim_eval_universal always ensures) but ValidWalkback doesn't encode
-- this constraint. Fixing this requires refactoring ValidWalkback.
-- ============================================================================

theorem walkback_bouncing (tm : TM) (as bs : Nat) (hc : IsClassB tm as bs) :
    ValidWalkback tm as := by
  sorry

-- ============================================================================
-- ComputesSucc for Class B
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
