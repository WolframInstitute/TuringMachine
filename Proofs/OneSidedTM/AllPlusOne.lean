/-
  OneSidedTM.AllPlusOne

  Formal proof that ALL 17 candidate {2,2} one-sided TM rules compute successor.

  Three structural classes:
  1. Rule 445 (carry + LEFT absorb): PlusOne.lean  ✓
  2. Class B (carry + RIGHT absorb): 8 rules, dead (2,1) — proved here  ✓
  3. Class C (skip + RIGHT absorb): 8 rules, dead (2,0) — proved in ClassC.lean  ✓
  4. Bulk computational: all 17 rules verified for n=1..65535  ✓
-/

import OneSidedTM.Basic
import OneSidedTM.PlusOne
import OneSidedTM.ClassC
import OneSidedTM.ClassW
import OneSidedTM.ClassSX
import OneSidedTM.ClassWL
import OneSidedTM.Decide

namespace OneSidedTM
open TM

-- ============================================================================
-- Part 1: Class B — carry + right-absorb (dead (2,1))
-- ============================================================================

/-- A TM is Class B: carry writes 0 on 1s, absorb writes 1 on 0s going R,
    return on 0s preserves tape. The (2,1) transition is dead. -/
structure IsClassB (tm : TM) : Prop where
  carry : tm.transition 1 1 = { nextState := 1, write := 0, dir := Dir.L }
  absorb : tm.transition 1 0 = { nextState := 2, write := 1, dir := Dir.R }
  ret0 : tm.transition 2 0 = { nextState := 2, write := 0, dir := Dir.R }

-- Return through all-zero positions: only uses (2,0), never (2,1)!
theorem return_zeros (tm : TM) (hc : IsClassB tm) (tape : List Nat) (p : Nat)
    (hlen : p < tape.length) (h0 : ∀ i, i ≤ p → readTape tape i = 0) :
    eval tm ⟨2, p, tape⟩ (p + 1) = some ⟨2, 0, tape⟩ := by
  induction p with
  | zero =>
    exact eval_step_halt tm _ _ 0 (by
      simp only [step, h0 0 (by omega), hc.ret0]
      simp [writeTape_val_eq_id tape 0 0 hlen (h0 0 (by omega))])
  | succ p ih =>
    have hr := h0 (p + 1) (by omega)
    have hs : step tm ⟨2, p + 1, tape⟩ = StepResult.continue ⟨2, p, tape⟩ := by
      simp only [step, hr, hc.ret0, Dir.R]
      have hne : (p + 1 == 0) = false := by simp
      rw [hne]; simp [writeTape_val_eq_id tape (p + 1) 0 hlen hr]
    rw [show (p + 1 + 1 : Nat) = (p + 1) + 1 from by omega,
        eval_step_continue tm _ _ (p + 1) hs]
    exact ih (by omega) (fun i hi => h0 i (by omega))

-- Tape reading helpers
private theorem rl_ (tape : List Nat) : readTape tape tape.length = 0 := by
  induction tape with
  | nil => simp [readTape, List.getD]
  | cons _ rest ih => simp [readTape_cons_succ, ih]

private theorem rs_ (pre : List Nat) (d : Nat) (suf : List Nat) :
    readTape (pre ++ d :: suf) pre.length = d := by
  induction pre with
  | nil => simp [readTape, List.getD]
  | cons _ rest ih => simp [readTape_cons_succ, ih]

private theorem rz_app (pre suf : List Nat) (hp : ∀ d ∈ pre, d = 0)
    (i : Nat) (hi : i < pre.length) : readTape (pre ++ suf) i = 0 := by
  induction pre generalizing i with
  | nil => simp at hi
  | cons d rest ih =>
    cases i with
    | zero => simp [readTape, List.getD]; exact hp d (List.mem_cons.mpr (.inl rfl))
    | succ j =>
      simp [readTape_cons_succ]
      exact ih (fun x hx => hp x (List.mem_cons.mpr (.inr hx))) j (by simp at hi; omega)

-- Core simulation for Class B with all-zeros prefix invariant
theorem sim_eval_B (tm : TM) (hc : IsClassB tm) (pre suf : List Nat)
    (hbp : ∀ d ∈ pre, d = 0)
    (hbs : ∀ d ∈ suf, d = 0 ∨ d = 1) :
    ∃ fuel cfg, eval tm ⟨1, pre.length, pre ++ suf⟩ fuel = some cfg ∧
    fromBinary cfg.tape = fromBinary (pre ++ binarySucc suf) := by
  induction suf generalizing pre with
  | nil =>
    by_cases hp : pre.length = 0
    · have hpnil := List.eq_nil_of_length_eq_zero hp; subst hpnil
      simp only [List.append_nil, List.nil_append, binarySucc]
      have hab : step tm ⟨1, 0, []⟩ = StepResult.halted ⟨2, 0, [1]⟩ := by
        simp only [step, show readTape [] 0 = 0 from by simp [readTape, List.getD], hc.absorb]
        rfl
      exact ⟨1, ⟨2, 0, [1]⟩, eval_step_halt tm _ _ 0 hab, rfl⟩
    · have hgt := Nat.pos_of_ne_zero hp
      simp only [List.append_nil]
      have hab : step tm ⟨1, pre.length, pre⟩ =
          StepResult.continue ⟨2, pre.length - 1, pre ++ [1]⟩ := by
        simp only [step, rl_ pre, hc.absorb, Dir.R]
        have hne : (pre.length == 0) = false := by
          cases pre with | nil => simp at hp | cons _ _ => simp
        rw [hne]; simp [writeTape]
      exact ⟨_, _, by
        rw [eval_step_continue tm _ _ _ hab,
            show pre.length = (pre.length - 1) + 1 from by omega]
        exact return_zeros tm hc (pre ++ [1]) (pre.length - 1) (by simp; omega)
          (fun i hi => rz_app pre [1] hbp i (by omega)), rfl⟩

  | cons d rest ih =>
    have hbr : ∀ x ∈ rest, x = 0 ∨ x = 1 := fun x hx => hbs x (List.mem_cons.mpr (.inr hx))
    rcases hbs d (List.mem_cons.mpr (.inl rfl)) with rfl | rfl
    · by_cases hp : pre.length = 0
      · have hpnil := List.eq_nil_of_length_eq_zero hp; subst hpnil; simp
        have hab : step tm ⟨1, 0, 0 :: rest⟩ = StepResult.halted ⟨2, 0, 1 :: rest⟩ := by
          simp only [step, show readTape (0 :: rest) 0 = 0 from by simp [readTape, List.getD],
                      hc.absorb]; simp [writeTape]
        exact ⟨1, _, eval_step_halt tm _ _ 0 hab, rfl⟩
      · have hgt := Nat.pos_of_ne_zero hp
        have hab : step tm ⟨1, pre.length, pre ++ 0 :: rest⟩ =
            StepResult.continue ⟨2, pre.length - 1, pre ++ 1 :: rest⟩ := by
          simp only [step, rs_ pre 0 rest, hc.absorb, Dir.R]
          have hne : (pre.length == 0) = false := by
            cases pre with | nil => simp at hp | cons _ _ => simp
          rw [hne]; simp [writeTape_append pre 0 rest 1]
        exact ⟨_, _, by
          rw [eval_step_continue tm _ _ _ hab,
              show pre.length = (pre.length - 1) + 1 from by omega]
          exact return_zeros tm hc (pre ++ 1 :: rest) (pre.length - 1) (by simp; omega)
            (fun i hi => rz_app pre (1 :: rest) hbp i (by omega)), rfl⟩

    · -- d = 1: carry + IH
      have hbp' : ∀ x ∈ pre ++ [0], x = 0 := by
        intro x hx; simp at hx; rcases hx with h | h; exact hbp x h; exact h
      obtain ⟨f, c, he, hf⟩ := ih (pre ++ [0]) hbp' hbr
      have hcarry : step tm ⟨1, pre.length, pre ++ 1 :: rest⟩ =
          StepResult.continue ⟨1, pre.length + 1, pre ++ 0 :: rest⟩ := by
        simp only [step, rs_ pre 1 rest, hc.carry]
        simp [writeTape_append pre 1 rest 0]
      exact ⟨_, _, by
        rw [eval_step_continue tm _ _ f hcarry,
            show pre.length + 1 = (pre ++ [0]).length from by simp,
            show pre ++ 0 :: rest = (pre ++ [0]) ++ rest from by simp]; exact he,
        by show fromBinary c.tape = fromBinary (pre ++ (0 :: binarySucc rest))
           rw [show pre ++ 0 :: binarySucc rest = (pre ++ [0]) ++ binarySucc rest from by simp]
           exact hf⟩

/-- Any Class B TM computes successor. -/
theorem classB_computesSucc (tm : TM) (hc : IsClassB tm) : ComputesSucc tm := by
  intro n _hn
  obtain ⟨fuel, cfg, heval, hfb⟩ :=
    sim_eval_B tm hc [] (toBinary n) (fun _ h => nomatch h) (toBinary_binary n)
  refine ⟨fuel, ?_⟩; simp at heval hfb
  simp only [run, initConfig, heval, Option.map, outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

-- ============================================================================
-- Part 2: Instances + bulk verification
-- ============================================================================

def rule509 : TM where
  numStates := 2; numSymbols := 2
  transition := fun s sy => match s, sy with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 2, 0 => { nextState := 2, write := 0, dir := Dir.R }
    | 2, 1 => { nextState := 2, write := 1, dir := Dir.R }
    | _, _ => { nextState := 2, write := 0, dir := Dir.R }

theorem r509_isClassB : IsClassB rule509 := ⟨rfl, rfl, rfl⟩
theorem rule509_computesSucc : ComputesSucc rule509 := classB_computesSucc rule509 r509_isClassB

-- Bulk verification for ALL 17 candidates
theorem all_candidates_bulk : ∀ r ∈ candidateRules, ∀ n ∈ List.range 65536,
    n = 0 ∨ run (fromRuleNumber r) n 200 = some (n + 1) := by native_decide

-- Class B instances (rules 453-509): carry + right-absorb, dead (2,1)
theorem r453_isClassB : IsClassB (fromRuleNumber 453) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r461_isClassB : IsClassB (fromRuleNumber 461) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r469_isClassB : IsClassB (fromRuleNumber 469) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r477_isClassB : IsClassB (fromRuleNumber 477) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r485_isClassB : IsClassB (fromRuleNumber 485) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r493_isClassB : IsClassB (fromRuleNumber 493) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r501_isClassB : IsClassB (fromRuleNumber 501) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r509_isClassB' : IsClassB (fromRuleNumber 509) := ⟨by native_decide, by native_decide, by native_decide⟩

theorem r453_succ : ComputesSucc (fromRuleNumber 453) := classB_computesSucc _ r453_isClassB
theorem r461_succ : ComputesSucc (fromRuleNumber 461) := classB_computesSucc _ r461_isClassB
theorem r469_succ : ComputesSucc (fromRuleNumber 469) := classB_computesSucc _ r469_isClassB
theorem r477_succ : ComputesSucc (fromRuleNumber 477) := classB_computesSucc _ r477_isClassB
theorem r485_succ : ComputesSucc (fromRuleNumber 485) := classB_computesSucc _ r485_isClassB
theorem r493_succ : ComputesSucc (fromRuleNumber 493) := classB_computesSucc _ r493_isClassB
theorem r501_succ : ComputesSucc (fromRuleNumber 501) := classB_computesSucc _ r501_isClassB
theorem r509_succ : ComputesSucc (fromRuleNumber 509) := classB_computesSucc _ r509_isClassB'

-- Class C instances (rules 1512-1519): skip + right-absorb, dead (2,0)
theorem r1512_isClassC : IsClassC (fromRuleNumber 1512) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r1513_isClassC : IsClassC (fromRuleNumber 1513) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r1514_isClassC : IsClassC (fromRuleNumber 1514) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r1515_isClassC : IsClassC (fromRuleNumber 1515) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r1516_isClassC : IsClassC (fromRuleNumber 1516) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r1517_isClassC : IsClassC (fromRuleNumber 1517) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r1518_isClassC : IsClassC (fromRuleNumber 1518) := ⟨by native_decide, by native_decide, by native_decide⟩
theorem r1519_isClassC : IsClassC (fromRuleNumber 1519) := ⟨by native_decide, by native_decide, by native_decide⟩

theorem r1512_succ : ComputesSucc (fromRuleNumber 1512) := classC_computesSucc _ r1512_isClassC
theorem r1513_succ : ComputesSucc (fromRuleNumber 1513) := classC_computesSucc _ r1513_isClassC
theorem r1514_succ : ComputesSucc (fromRuleNumber 1514) := classC_computesSucc _ r1514_isClassC
theorem r1515_succ : ComputesSucc (fromRuleNumber 1515) := classC_computesSucc _ r1515_isClassC
theorem r1516_succ : ComputesSucc (fromRuleNumber 1516) := classC_computesSucc _ r1516_isClassC
theorem r1517_succ : ComputesSucc (fromRuleNumber 1517) := classC_computesSucc _ r1517_isClassC
theorem r1518_succ : ComputesSucc (fromRuleNumber 1518) := classC_computesSucc _ r1518_isClassC
theorem r1519_succ : ComputesSucc (fromRuleNumber 1519) := classC_computesSucc _ r1519_isClassC

end OneSidedTM
