/-
  OneSidedTM.ClassD

  Class D (Delegation) one-sided TMs.
  State 1 delegates carry/scan to state cs ∈ {2,3}.

  Two variants:
  - ClassDW: carry delegation — (1,1) → {cs, 0, L}
  - ClassDS: scan delegation  — (1,1) → {cs, 1, L}
-/

import OneSidedTM.Basic
import OneSidedTM.PlusOne
import OneSidedTM.ClassW
import OneSidedTM.ClassSX

namespace OneSidedTM
open TM

-- ============================================================================
-- Carry Delegation: (1,1) → {cs, 0, L}
-- ============================================================================

/-- Carry delegation: state 1 absorbs on 0 and delegates carry to cs on 1. -/
theorem sim_eval_delegate (tm : TM) (cs as : Nat)
    (habsorb1 : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R })
    (hdelegate : tm.transition 1 1 = { nextState := cs, write := 0, dir := Dir.L })
    (hcarry_cs : tm.transition cs 1 = { nextState := cs, write := 0, dir := Dir.L })
    (habsorb_cs : tm.transition cs 0 = { nextState := as, write := 1, dir := Dir.R })
    (hwalkback : ValidWalkback tm as)
    (n : Nat) (suf : List Nat)
    (hbs : ∀ d ∈ suf, d = 0 ∨ d = 1) :
    ∃ fuel cfg, eval tm ⟨1, n, List.replicate n 0 ++ suf⟩ fuel = some cfg ∧
    fromBinary cfg.tape = fromBinary (List.replicate n 0 ++ binarySucc suf) := by
  induction suf generalizing n with
  | nil =>
    simp only [List.append_nil, binarySucc]
    cases n with
    | zero =>
      have hs : step tm ⟨1, 0, []⟩ = StepResult.halted ⟨as, 0, [1]⟩ := by
        simp [step, readTape, List.getD, habsorb1, writeTape, List.set]
      exact ⟨1, ⟨as, 0, [1]⟩, eval_step_halt _ _ _ 0 hs, by simp [fromBinary]⟩
    | succ m =>
      have hr : readTape (List.replicate (m + 1) 0) (m + 1) = 0 := rt_beyond _ _ (by simp)
      have hwt := wt_rep_extend (m + 1) 1
      have h_m0 : (m + 1 == 0) = false := by simp
      have ha : step tm ⟨1, m + 1, List.replicate (m + 1) 0⟩ =
          StepResult.continue ⟨as, m, List.replicate (m + 1) 0 ++ [1]⟩ := by
        unfold step; simp [hr, habsorb1, h_m0, hwt]
      obtain ⟨fw, es, he⟩ := hwalkback (m + 1) [1] m (by omega) (by simp) (by simp)
      exact ⟨fw + 1, ⟨es, 0, List.replicate (m + 1) 0 ++ [1]⟩,
        by rw [eval_step_continue _ _ _ _ ha]; exact he, rfl⟩
  | cons d rest ih =>
    have hbr : ∀ x ∈ rest, x = 0 ∨ x = 1 := fun x hx => hbs x (List.mem_cons.mpr (.inr hx))
    rcases hbs d (List.mem_cons.mpr (.inl rfl)) with rfl | rfl
    · simp only [binarySucc]
      cases n with
      | zero =>
        have hs : step tm ⟨1, 0, 0 :: rest⟩ = StepResult.halted ⟨as, 0, 1 :: rest⟩ := by
          simp [step, readTape, List.getD, habsorb1, writeTape, List.set]
        exact ⟨1, ⟨as, 0, 1 :: rest⟩, eval_step_halt _ _ _ 0 hs, by simp [fromBinary]⟩
      | succ m =>
        have hr := rt_split (m + 1) 0 rest
        have h_m0 : (m + 1 == 0) = false := by simp
        have ha : step tm ⟨1, m + 1, List.replicate (m + 1) 0 ++ 0 :: rest⟩ =
            StepResult.continue ⟨as, m, List.replicate (m + 1) 0 ++ 1 :: rest⟩ := by
          unfold step; simp [hr, habsorb1, h_m0, wt_split]
        obtain ⟨fw, es, he⟩ := hwalkback (m + 1) (1 :: rest) m (by omega) (by
          intro x hx; simp at hx; cases hx with | inl h => exact Or.inr h | inr h => exact hbr x h) (by simp)
        exact ⟨fw + 1, ⟨es, 0, List.replicate (m + 1) 0 ++ 1 :: rest⟩,
          by rw [eval_step_continue _ _ _ _ ha]; exact he, rfl⟩
    · -- d = 1: DELEGATE to cs
      have hrd := rt_split n 1 rest
      have ha : step tm ⟨1, n, List.replicate n 0 ++ 1 :: rest⟩ =
          StepResult.continue ⟨cs, n + 1, List.replicate (n + 1) 0 ++ rest⟩ := by
        simp [step, hrd, hdelegate, wt_split, ← rep_snoc, List.append_assoc]
      obtain ⟨f, c, he, hf⟩ := sim_eval_carry tm cs as hcarry_cs habsorb_cs hwalkback (n + 1) rest hbr
      exact ⟨f + 1, c,
        by rw [eval_step_continue _ _ _ _ ha]; exact he,
        by rw [hf, show binarySucc (1 :: rest) = 0 :: binarySucc rest from rfl,
               ← rep_snoc n 0, List.append_assoc]; rfl⟩

-- ============================================================================
-- ComputesSucc facades
-- ============================================================================

/-- Carry delegation structure. -/
structure IsClassDW (tm : TM) (cs as : Nat) : Prop where
  absorb1  : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R }
  delegate : tm.transition 1 1 = { nextState := cs, write := 0, dir := Dir.L }
  carry    : tm.transition cs 1 = { nextState := cs, write := 0, dir := Dir.L }
  absorb   : tm.transition cs 0 = { nextState := as, write := 1, dir := Dir.R }

theorem classDW_computesSucc (tm : TM) (cs as : Nat)
    (hc : IsClassDW tm cs as) (hwalk : ValidWalkback tm as) :
    ComputesSucc tm := by
  intro n _hn
  obtain ⟨fuel, cfg, heval, hfb⟩ :=
    sim_eval_delegate tm cs as hc.absorb1 hc.delegate hc.carry hc.absorb hwalk
      0 (toBinary n) (toBinary_binary n)
  refine ⟨fuel, ?_⟩; simp at heval hfb
  simp only [run, initConfig, heval, Option.map, outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

/-- Scan delegation structure. -/
structure IsClassDS (tm : TM) (cs as : Nat) : Prop where
  absorb1  : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R }
  delegate : tm.transition 1 1 = { nextState := cs, write := 1, dir := Dir.L }
  scan     : tm.transition cs 1 = { nextState := cs, write := 1, dir := Dir.L }
  absorb   : tm.transition cs 0 = { nextState := as, write := 1, dir := Dir.R }

theorem classDS_computesSucc (tm : TM) (cs as : Nat)
    (hc : IsClassDS tm cs as)
    (hclearback : ValidClearbackG tm as) :
    ComputesSucc tm := by
  intro n _hn
  obtain ⟨fuel, cfg, heval, hfb⟩ :=
    sim_eval_scan_delegate tm cs as hc.absorb1 hc.delegate hc.scan hc.absorb hclearback
      [] (toBinary n) (fun _ h => nomatch h) (toBinary_binary n)
  refine ⟨fuel, ?_⟩; simp at heval hfb
  simp only [run, initConfig, heval, Option.map, outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

end OneSidedTM
