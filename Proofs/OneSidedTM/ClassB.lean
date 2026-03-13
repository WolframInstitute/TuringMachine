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
-- Helpers
-- ============================================================================

/-- All elements of List.replicate n 0 ++ suf are 0 or 1, given suf is binary -/
private theorem all_binary_rep_suf (n : Nat) (suf : List Nat)
    (hbs : ∀ d ∈ suf, d = 0 ∨ d = 1) :
    ∀ d ∈ (List.replicate n 0 ++ suf), d = 0 ∨ d = 1 := by
  intro d hd; simp [List.mem_append] at hd
  rcases hd with ⟨_, rfl⟩ | hd
  · exact Or.inl rfl
  · exact hbs d hd

/-- readTape returns 0 or 1 on a tape whose elements are all 0 or 1 -/
private theorem readTape_binary_tape (tape : List Nat) (pos : Nat)
    (hall : ∀ d ∈ tape, d = 0 ∨ d = 1) :
    readTape tape pos = 0 ∨ readTape tape pos = 1 := by
  unfold readTape; unfold List.getD
  cases h : tape.get? pos with
  | none => left; rfl
  | some x => exact hall x (List.mem_of_get? h)

/-- Corollary for the zero-prefix ++ binary-suffix tapes used in walkback -/
private theorem readTape_rep_suf_binary (n : Nat) (suf : List Nat) (pos : Nat)
    (hbs : ∀ d ∈ suf, d = 0 ∨ d = 1) :
    readTape (List.replicate n 0 ++ suf) pos = 0 ∨
    readTape (List.replicate n 0 ++ suf) pos = 1 :=
  readTape_binary_tape _ pos (all_binary_rep_suf n suf hbs)

-- ============================================================================
-- Walkback proof
-- ============================================================================

/-- The bouncing walkback preserves the tape and returns to position 0.
    Each position takes 3 steps: write 1 + bounce left/right + clear 1 + advance.
    Requires suf.length > 0 so the bounce doesn't extend the tape at boundary. -/
theorem walkback_bouncing (tm : TM) (as bs : Nat) (hc : IsClassB tm as bs) :
    ValidWalkback tm as := by
  intro n suf pos hpos hbs hsuf
  -- Key: tape.length = n + suf.length ≥ n + 1 > pos + 1
  -- So the bounce at pos+1 is always in-bounds.
  have htl : (List.replicate n 0 ++ suf).length = n + suf.length := by simp
  induction pos with
  | zero =>
    have h0 : readTape (List.replicate n 0 ++ suf) 0 = 0 := rt_zeros n suf 0 (by omega)
    -- Step 1: (as,0) at 0 → (bs,1,L) → write 1, go to 1
    have hs1 : step tm ⟨as, 0, List.replicate n 0 ++ suf⟩ =
        StepResult.continue ⟨bs, 1, writeTape (List.replicate n 0 ++ suf) 0 1⟩ := by
      simp [step, h0, hc.walk_L]
    -- tape'[1] is unchanged from tape[1], and is 0 or 1
    have hr1 : readTape (writeTape (List.replicate n 0 ++ suf) 0 1) 1 =
        readTape (List.replicate n 0 ++ suf) 1 :=
      read_write_other (List.replicate n 0 ++ suf) 0 1 1 (by omega)
    have hbin1 : readTape (writeTape (List.replicate n 0 ++ suf) 0 1) 1 = 0 ∨
                 readTape (writeTape (List.replicate n 0 ++ suf) 0 1) 1 = 1 := by
      rw [hr1]; exact readTape_rep_suf_binary n suf 1 hbs
    -- tape'.length ≥ n + 1 ≥ 2
    have hlen1 : 1 < (writeTape (List.replicate n 0 ++ suf) 0 1).length := by
      rw [writeTape_length]; omega
    -- Step 2: bs at 1, reads ∈ {0,1}, writes same (nop), goes R to 0
    have hs2 : step tm ⟨bs, 1, writeTape (List.replicate n 0 ++ suf) 0 1⟩ =
        StepResult.continue ⟨as, 0, writeTape (List.replicate n 0 ++ suf) 0 1⟩ := by
      rcases hbin1 with h0v | h1v
      · simp only [step, h0v, hc.walk_R_0]
        rw [writeTape_val_eq_id _ 1 0 hlen1 h0v]
        simp [show (1 : Nat) ≠ 0 from by omega]
      · simp only [step, h1v, hc.walk_R_1]
        rw [writeTape_val_eq_id _ 1 1 hlen1 h1v]
        simp [show (1 : Nat) ≠ 0 from by omega]
    -- Step 3: (as,1) at 0 → halt
    have hr0 : readTape (writeTape (List.replicate n 0 ++ suf) 0 1) 0 = 1 :=
      read_write_self (List.replicate n 0 ++ suf) 0 1
    have hw_restore : writeTape (writeTape (List.replicate n 0 ++ suf) 0 1) 0 0 =
        List.replicate n 0 ++ suf := by
      rw [write_write_eq]; exact writeTape_val_eq_id _ 0 0 (by omega) h0
    have hs3 : step tm ⟨as, 0, writeTape (List.replicate n 0 ++ suf) 0 1⟩ =
        StepResult.halted ⟨as, 0, List.replicate n 0 ++ suf⟩ := by
      unfold step; simp [hr0, hc.walk_clr, hw_restore]
    exact ⟨3, as, by
      rw [show (3 : Nat) = 2 + 1 from rfl, eval_step_continue _ _ _ _ hs1,
          show (2 : Nat) = 1 + 1 from rfl, eval_step_continue _ _ _ _ hs2,
          eval_step_halt _ _ _ 0 hs3]⟩

  | succ p ih =>
    have hz : readTape (List.replicate n 0 ++ suf) (p + 1) = 0 := rt_zeros n suf (p + 1) (by omega)
    -- Step 1: (as,0) at p+1 → (bs,1,L) → write 1 at p+1, go to p+2
    have hs1 : step tm ⟨as, p + 1, List.replicate n 0 ++ suf⟩ =
        StepResult.continue ⟨bs, p + 2, writeTape (List.replicate n 0 ++ suf) (p + 1) 1⟩ := by
      simp [step, hz, hc.walk_L]
    -- tape'[p+2] unchanged, is 0 or 1
    have hr2 : readTape (writeTape (List.replicate n 0 ++ suf) (p + 1) 1) (p + 2) =
        readTape (List.replicate n 0 ++ suf) (p + 2) :=
      read_write_other (List.replicate n 0 ++ suf) (p + 1) (p + 2) 1 (by omega)
    have hbin2 : readTape (writeTape (List.replicate n 0 ++ suf) (p + 1) 1) (p + 2) = 0 ∨
                 readTape (writeTape (List.replicate n 0 ++ suf) (p + 1) 1) (p + 2) = 1 := by
      rw [hr2]; exact readTape_rep_suf_binary n suf (p + 2) hbs
    -- p + 2 < tape'.length (since p+1 < n + 1 ≤ n + |suf|)
    have hlen2 : p + 2 < (writeTape (List.replicate n 0 ++ suf) (p + 1) 1).length := by
      rw [writeTape_length]; omega
    -- Step 2: bs at p+2, reads ∈ {0,1}, writes same (nop), goes R to p+1
    have hs2 : step tm ⟨bs, p + 2, writeTape (List.replicate n 0 ++ suf) (p + 1) 1⟩ =
        StepResult.continue ⟨as, p + 1, writeTape (List.replicate n 0 ++ suf) (p + 1) 1⟩ := by
      rcases hbin2 with h0v | h1v
      · simp only [step, h0v, hc.walk_R_0]
        rw [writeTape_val_eq_id _ (p + 2) 0 hlen2 h0v]
        simp [show (p + 2 : Nat) ≠ 0 from by omega, show p + 2 - 1 = p + 1 from by omega]
      · simp only [step, h1v, hc.walk_R_1]
        rw [writeTape_val_eq_id _ (p + 2) 1 hlen2 h1v]
        simp [show (p + 2 : Nat) ≠ 0 from by omega, show p + 2 - 1 = p + 1 from by omega]
    -- Step 3: (as,1) at p+1 → (as,0,R) → continue to p, tape restored
    have hr1 : readTape (writeTape (List.replicate n 0 ++ suf) (p + 1) 1) (p + 1) = 1 :=
      read_write_self (List.replicate n 0 ++ suf) (p + 1) 1
    have hw_restore : writeTape (writeTape (List.replicate n 0 ++ suf) (p + 1) 1) (p + 1) 0 =
        List.replicate n 0 ++ suf := by
      rw [write_write_eq]; exact writeTape_val_eq_id _ (p + 1) 0 (by omega) hz
    have hs3 : step tm ⟨as, p + 1, writeTape (List.replicate n 0 ++ suf) (p + 1) 1⟩ =
        StepResult.continue ⟨as, p, List.replicate n 0 ++ suf⟩ := by
      unfold step; simp [hr1, hc.walk_clr, hw_restore,
        show (p + 1 == 0) = false from by simp, show p + 1 - 1 = p from by omega]
    -- IH
    obtain ⟨f, es, he⟩ := ih (by omega)
    exact ⟨f + 3, es, by
      rw [show f + 3 = ((f + 1) + 1) + 1 from by omega,
          eval_step_continue _ _ _ _ hs1, eval_step_continue _ _ _ _ hs2,
          eval_step_continue _ _ _ _ hs3]
      exact he⟩

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

-- Rule 155321: IsClassB with as=2, bs=3
def rule155321 : TM := fromRuleNumber32 155321

theorem rule155321_isClassB : IsClassB rule155321 2 3 := {
  carry    := rfl
  absorb   := rfl
  walk_L   := rfl
  walk_R_0 := rfl
  walk_R_1 := rfl
  walk_clr := rfl
}

theorem rule155321_computesSucc : ComputesSucc rule155321 :=
  classB_computes rule155321 2 3 rule155321_isClassB

end OneSidedTM
