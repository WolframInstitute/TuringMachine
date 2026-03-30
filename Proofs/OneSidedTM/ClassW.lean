/-
  OneSidedTM.ClassW

  Class W (Carry+Walkback) one-sided TMs: carry phase + absorb + walkback over zeros.
  This covers the Rule 146514 algorithm family (Groups 8 and 17).

  Algorithm:
  1. Carry phase: state 1 reads 1, writes 0, moves L (towards MSB).
  2. Absorb: state 1 reads 0, writes 1, moves R, enters walk state `as`.
  3. Walkback: scans zeros moving R until halting at position 0.

  There are 3 main walkback structures observed:
  - Self-loop: `(as, 0) → {as, 0, R}`
  - Toggle: `(as, 0) → {bs, 0, R}`, `(bs, 0) → {as, 0, R}` (Rule 146514 variant)
  - Drop: `(as, 0) → {bs, 0, R}`, `(bs, 0) → {bs, 0, R}`
-/

import OneSidedTM.Basic
import OneSidedTM.PlusOne

namespace OneSidedTM
open TM

-- ============================================================================
-- The 3 structural variants
-- ============================================================================

structure IsClassW_Self (tm : TM) (as : Nat) : Prop where
  carry  : tm.transition 1 1 = { nextState := 1,  write := 0, dir := Dir.L }
  absorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R }
  walk   : tm.transition as 0 = { nextState := as, write := 0, dir := Dir.R }

structure IsClassW_Toggle (tm : TM) (as bs : Nat) : Prop where
  carry  : tm.transition 1 1 = { nextState := 1,  write := 0, dir := Dir.L }
  absorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R }
  walkA  : tm.transition as 0 = { nextState := bs, write := 0, dir := Dir.R }
  walkB  : tm.transition bs 0 = { nextState := as, write := 0, dir := Dir.R }

structure IsClassW_Drop (tm : TM) (as bs : Nat) : Prop where
  carry  : tm.transition 1 1 = { nextState := 1,  write := 0, dir := Dir.L }
  absorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R }
  walkA  : tm.transition as 0 = { nextState := bs, write := 0, dir := Dir.R }
  walkB  : tm.transition bs 0 = { nextState := bs, write := 0, dir := Dir.R }


-- ============================================================================
-- Walkback proofs
-- ============================================================================

-- Walkback proof for SelfLoop
theorem walkback_self (tm : TM) (as : Nat) (hc : IsClassW_Self tm as) :
    ValidWalkback tm as := by
  intro n suf pos hpos _hbs _hsuf
  induction pos with
  | zero =>
    have h0 := rt_zeros n suf 0 (by omega)
    have hwt : writeTape (List.replicate n 0 ++ suf) 0 0 = List.replicate n 0 ++ suf :=
      writeTape_val_eq_id _ 0 0 (by simp; omega) h0
    have hs : step tm ⟨as, 0, List.replicate n 0 ++ suf⟩ =
        StepResult.halted ⟨as, 0, List.replicate n 0 ++ suf⟩ := by
      simp [step, h0, hc.walk, hwt]
    exact ⟨1, as, eval_step_halt _ _ _ 0 (by simp [step, h0, hc.walk]; rw [hwt])⟩
  | succ p ih =>
    have hz := rt_zeros n suf (p + 1) (by omega)
    have hwt : writeTape (List.replicate n 0 ++ suf) (p + 1) 0 = List.replicate n 0 ++ suf :=
      writeTape_val_eq_id _ (p + 1) 0 (by simp; omega) hz
    have hs : step tm ⟨as, p + 1, List.replicate n 0 ++ suf⟩ =
        StepResult.continue ⟨as, p, List.replicate n 0 ++ suf⟩ := by
      simp only [step, hz, hc.walk]
      have hfalse : (p + 1 == 0) = false := by simp
      simp [hfalse, hwt]
    obtain ⟨f, es, he⟩ := ih (by omega)
    exact ⟨f + 1, es, by rw [eval_step_continue _ _ _ _ hs]; exact he⟩

-- Walkback proof for Toggle
theorem walkback_toggle (tm : TM) (as bs : Nat) (hc : IsClassW_Toggle tm as bs) :
    ValidWalkback tm as ∧ ValidWalkback tm bs := by
  have H : ∀ pos n suf, pos < n → ∀ s, (s = as ∨ s = bs) →
      ∃ fuel endState, eval tm ⟨s, pos, List.replicate n 0 ++ suf⟩ fuel =
        some ⟨endState, 0, List.replicate n 0 ++ suf⟩ := by
    intro pos
    induction pos with
    | zero =>
      intro n suf hn s hs
      have h0 := rt_zeros n suf 0 (by omega)
      have hwt : writeTape (List.replicate n 0 ++ suf) 0 0 = List.replicate n 0 ++ suf :=
        writeTape_val_eq_id _ 0 0 (by simp; omega) h0
      rcases hs with rfl | rfl
      · exact ⟨1, bs, eval_step_halt _ _ _ 0 (by simp [step, h0, hc.walkA]; rw [hwt])⟩
      · exact ⟨1, as, eval_step_halt _ _ _ 0 (by simp [step, h0, hc.walkB]; rw [hwt])⟩
    | succ p ih =>
      intro n suf hn s hs
      have hz := rt_zeros n suf (p + 1) (by omega)
      have hwt : writeTape (List.replicate n 0 ++ suf) (p + 1) 0 = List.replicate n 0 ++ suf :=
        writeTape_val_eq_id _ (p + 1) 0 (by simp; omega) hz
      rcases hs with hA | hB
      · have hsStep : step tm ⟨s, p + 1, List.replicate n 0 ++ suf⟩ =
            StepResult.continue ⟨bs, p, List.replicate n 0 ++ suf⟩ := by
          simp only [step, hA, hz, hc.walkA]
          have hfalse : (p + 1 == 0) = false := by simp
          simp [hfalse, hwt]
        obtain ⟨f, es, he⟩ := ih n suf (by omega) bs (Or.inr rfl)
        exact ⟨f + 1, es, by rw [eval_step_continue _ _ _ _ hsStep]; exact he⟩
      · have hsStep : step tm ⟨s, p + 1, List.replicate n 0 ++ suf⟩ =
            StepResult.continue ⟨as, p, List.replicate n 0 ++ suf⟩ := by
          simp only [step, hB, hz, hc.walkB]
          have hfalse : (p + 1 == 0) = false := by simp
          simp [hfalse, hwt]
        obtain ⟨f, es, he⟩ := ih n suf (by omega) as (Or.inl rfl)
        exact ⟨f + 1, es, by rw [eval_step_continue _ _ _ _ hsStep]; exact he⟩
  exact ⟨fun n suf pos hpos _hbs _hsuf => H pos n suf hpos as (Or.inl rfl),
         fun n suf pos hpos _hbs _hsuf => H pos n suf hpos bs (Or.inr rfl)⟩


-- We can just prove bs walkback separately.
private theorem walkback_drop_bs (tm : TM) (bs : Nat)
    (hwalk : tm.transition bs 0 = { nextState := bs, write := 0, dir := Dir.R }) :
    ValidWalkback tm bs := by
  intro n suf pos hpos _hbs _hsuf
  induction pos with
  | zero =>
    have h0 := rt_zeros n suf 0 (by omega)
    have hwt : writeTape (List.replicate n 0 ++ suf) 0 0 = List.replicate n 0 ++ suf :=
      writeTape_val_eq_id _ 0 0 (by simp; omega) h0
    exact ⟨1, bs, eval_step_halt _ _ _ 0 (by simp [step, h0, hwalk]; rw [hwt])⟩
  | succ p ih =>
    have hz := rt_zeros n suf (p + 1) (by omega)
    have hwt : writeTape (List.replicate n 0 ++ suf) (p + 1) 0 = List.replicate n 0 ++ suf :=
      writeTape_val_eq_id _ (p + 1) 0 (by simp; omega) hz
    have hs : step tm ⟨bs, p + 1, List.replicate n 0 ++ suf⟩ =
        StepResult.continue ⟨bs, p, List.replicate n 0 ++ suf⟩ := by
      simp only [step, hz, hwalk]
      have hfalse : (p + 1 == 0) = false := by simp
      simp [hfalse, hwt]
    obtain ⟨f, es, he⟩ := ih (by omega)
    exact ⟨f + 1, es, by rw [eval_step_continue _ _ _ _ hs]; exact he⟩

theorem walkback_drop_full (tm : TM) (as bs : Nat) (hc : IsClassW_Drop tm as bs) :
    ValidWalkback tm as := by
  intro n suf pos hpos hbs _hsuf
  cases pos with
  | zero =>
    have h0 := rt_zeros n suf 0 (by omega)
    have hwt : writeTape (List.replicate n 0 ++ suf) 0 0 = List.replicate n 0 ++ suf :=
      writeTape_val_eq_id _ 0 0 (by simp; omega) h0
    exact ⟨1, bs, eval_step_halt _ _ _ 0 (by simp [step, h0, hc.walkA]; rw [hwt])⟩
  | succ p =>
    have hz := rt_zeros n suf (p + 1) (by omega)
    have hwt : writeTape (List.replicate n 0 ++ suf) (p + 1) 0 = List.replicate n 0 ++ suf :=
      writeTape_val_eq_id _ (p + 1) 0 (by simp; omega) hz
    have hs1 : step tm ⟨as, p + 1, List.replicate n 0 ++ suf⟩ =
        StepResult.continue ⟨bs, p, List.replicate n 0 ++ suf⟩ := by
      simp only [step, hz, hc.walkA]
      have hfalse : (p + 1 == 0) = false := by simp
      simp [hfalse, hwt]
    obtain ⟨f, es, he⟩ := walkback_drop_bs tm bs hc.walkB n suf p (by omega) hbs _hsuf
    exact ⟨f + 1, es, by rw [eval_step_continue _ _ _ _ hs1]; exact he⟩

-- ============================================================================
-- The 3 structural proofs of ComputesSucc
-- ============================================================================

theorem classW_self_computes (tm : TM) (as : Nat) (hc : IsClassW_Self tm as) :
    ComputesSucc tm := by
  intro n _hn
  obtain ⟨fw, cfg, hev, hfb⟩ :=
    sim_eval_universal tm as hc.carry hc.absorb (walkback_self tm as hc) 0 (toBinary n) (toBinary_binary n)
  refine ⟨fw, ?_⟩
  simp at hev hfb
  simp only [run, initConfig, hev, Option.map]
  simp only [outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

theorem classW_toggle_computes (tm : TM) (as bs : Nat) (hc : IsClassW_Toggle tm as bs) :
    ComputesSucc tm := by
  intro n _hn
  obtain ⟨fw, cfg, hev, hfb⟩ :=
    sim_eval_universal tm as hc.carry hc.absorb (walkback_toggle tm as bs hc).1 0 (toBinary n) (toBinary_binary n)
  refine ⟨fw, ?_⟩
  simp at hev hfb
  simp only [run, initConfig, hev, Option.map]
  simp only [outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

theorem classW_drop_computes (tm : TM) (as bs : Nat) (hc : IsClassW_Drop tm as bs) :
    ComputesSucc tm := by
  intro n _hn
  obtain ⟨fw, cfg, hev, hfb⟩ :=
    sim_eval_universal tm as hc.carry hc.absorb (walkback_drop_full tm as bs hc) 0 (toBinary n) (toBinary_binary n)
  refine ⟨fw, ?_⟩
  simp at hev hfb
  simp only [run, initConfig, hev, Option.map]
  simp only [outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

-- ============================================================================
-- Concrete Implementations (Groups 8 and 17)
-- ============================================================================

-- Group 8 Self-loop variant (1728 rules)
def exampleW8Self : TM where
  numStates := 3
  numSymbols := 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 2, 0 => { nextState := 2, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.L }

theorem exampleW8Self_computesSucc : ComputesSucc exampleW8Self :=
  classW_self_computes exampleW8Self 2 ⟨rfl, rfl, rfl⟩

-- Group 8 Toggle variant (144 rules, includes Rule 146514)
def exampleW8Toggle : TM where
  numStates := 3
  numSymbols := 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 2, 0 => { nextState := 3, write := 0, dir := Dir.R }
    | 3, 0 => { nextState := 2, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.L }

theorem exampleW8Toggle_computesSucc : ComputesSucc exampleW8Toggle :=
  classW_toggle_computes exampleW8Toggle 2 3 ⟨rfl, rfl, rfl, rfl⟩

-- Group 8 Drop variant (144 rules)
def exampleW8Drop : TM where
  numStates := 3
  numSymbols := 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 2, 0 => { nextState := 3, write := 0, dir := Dir.R }
    | 3, 0 => { nextState := 3, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.L }

theorem exampleW8Drop_computesSucc : ComputesSucc exampleW8Drop :=
  classW_drop_computes exampleW8Drop 2 3 ⟨rfl, rfl, rfl, rfl⟩

-- Group 17 Self-loop variant (1728 rules)
def exampleW17Self : TM where
  numStates := 3
  numSymbols := 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 3, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 3, 0 => { nextState := 3, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.L }

theorem exampleW17Self_computesSucc : ComputesSucc exampleW17Self :=
  classW_self_computes exampleW17Self 3 ⟨rfl, rfl, rfl⟩

-- Group 17 Toggle variant (144 rules)
def exampleW17Toggle : TM where
  numStates := 3
  numSymbols := 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 3, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 3, 0 => { nextState := 2, write := 0, dir := Dir.R }
    | 2, 0 => { nextState := 3, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.L }

theorem exampleW17Toggle_computesSucc : ComputesSucc exampleW17Toggle :=
  classW_toggle_computes exampleW17Toggle 3 2 ⟨rfl, rfl, rfl, rfl⟩

-- Group 17 Drop variant (144 rules)
def exampleW17Drop : TM where
  numStates := 3
  numSymbols := 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 3, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 3, 0 => { nextState := 2, write := 0, dir := Dir.R }
    | 2, 0 => { nextState := 2, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.L }

theorem exampleW17Drop_computesSucc : ComputesSucc exampleW17Drop :=
  classW_drop_computes exampleW17Drop 3 2 ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- Rule-numbered instances via fromRuleNumber32
-- ============================================================================

theorem r145872_succ : ComputesSucc (fromRuleNumber32 145872) :=
  classW_self_computes (fromRuleNumber32 145872) 2 ⟨rfl, rfl, rfl⟩

theorem r146453_succ : ComputesSucc (fromRuleNumber32 146453) :=
  classW_toggle_computes (fromRuleNumber32 146453) 2 3 ⟨rfl, rfl, rfl, rfl⟩

theorem r146457_succ : ComputesSucc (fromRuleNumber32 146457) :=
  classW_drop_computes (fromRuleNumber32 146457) 2 3 ⟨rfl, rfl, rfl, rfl⟩

theorem r228105_succ : ComputesSucc (fromRuleNumber32 228105) :=
  classW_self_computes (fromRuleNumber32 228105) 3 ⟨rfl, rfl, rfl⟩

theorem r229397_succ : ComputesSucc (fromRuleNumber32 229397) :=
  classW_toggle_computes (fromRuleNumber32 229397) 3 2 ⟨rfl, rfl, rfl, rfl⟩

theorem r228821_succ : ComputesSucc (fromRuleNumber32 228821) :=
  classW_drop_computes (fromRuleNumber32 228821) 3 2 ⟨rfl, rfl, rfl, rfl⟩

end OneSidedTM
