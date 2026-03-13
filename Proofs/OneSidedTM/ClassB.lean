/-
  OneSidedTM.ClassB

  Class B (Carry+Bouncing Walkback) one-sided TMs.
  This covers Unknown Groups 1 and 2 (e.g., Rule 248514).
-/

import OneSidedTM.Basic
import OneSidedTM.PlusOne
import OneSidedTM.ClassW

namespace OneSidedTM
open TM

structure IsClassB (tm : TM) (as bs : Nat) : Prop where
  carry    : tm.transition 1 1 = { nextState := 1,  write := 0, dir := Dir.L }
  absorb   : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R }
  walk_L   : tm.transition as 0 = { nextState := bs, write := 1, dir := Dir.L }
  walk_R_0 : tm.transition bs 0 = { nextState := as, write := 0, dir := Dir.R }
  walk_R_1 : tm.transition bs 1 = { nextState := as, write := 1, dir := Dir.R }
  walk_clr : tm.transition as 1 = { nextState := as, write := 0, dir := Dir.R }

-- Helper lemmas for tape manipulation
private theorem rt_zeros (n : Nat) (suf : List Nat) (i : Nat) (h : i < n) :
    readTape (List.replicate n 0 ++ suf) i = 0 := by
  induction n generalizing i with
  | zero => omega
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (0 :: List.replicate m 0) ++ suf =
      0 :: (List.replicate m 0 ++ suf) from by simp]
    cases i with
    | zero => simp [readTape_cons_zero]
    | succ j => simp only [readTape_cons_succ]; exact ih j (by omega)

private theorem wt_zeros_id (n : Nat) (suf : List Nat) (i : Nat) (h : i < n) :
    writeTape (List.replicate n 0 ++ suf) i 0 = List.replicate n 0 ++ suf := by
  have hz := rt_zeros n suf i h
  exact writeTape_val_eq_id _ i 0 (by simp; omega) hz

private theorem readTape_replicate_append_eq (n v : Nat) :
    readTape (List.replicate n 0 ++ [v]) n = v := by
  induction n with
  | zero => simp [readTape, List.getD]
  | succ m ih =>
    rw [List.replicate_succ]
    show readTape (0 :: (List.replicate m 0 ++ [v])) (m + 1) = v
    rw [readTape_cons_succ]; exact ih

private theorem readTape_replicate_ne (n j v : Nat) (h : n ≠ j) :
    readTape (List.replicate n 0 ++ [v]) j = 0 := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => exact absurd rfl h
    | succ j' => simp [readTape, List.getD]
  | succ m ih =>
    rw [List.replicate_succ]
    show readTape (0 :: (List.replicate m 0 ++ [v])) j = 0
    cases j with
    | zero => rw [readTape_cons_zero]
    | succ j' => rw [readTape_cons_succ]; exact ih j' (by omega)

private theorem read_write_other (tape : List Nat) (i j v : Nat) (h : i ≠ j) :
    readTape (writeTape tape i v) j = readTape tape j := by
  induction tape generalizing i j with
  | nil =>
    simp only [writeTape, List.length_nil, Nat.not_lt_zero, ↓reduceIte, List.nil_append, Nat.sub_zero]
    rw [readTape_replicate_ne i j v h, readTape_nil]
  | cons d rest ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl h
      | succ j' => simp [writeTape_cons_zero, readTape_cons_succ]
    | succ i' =>
      cases j with
      | zero => simp [writeTape_cons_succ, readTape_cons_zero]
      | succ j' =>
        simp only [writeTape_cons_succ, readTape_cons_succ]
        exact ih i' j' (by omega)

private theorem write_write_eq (tape : List Nat) (i v1 v2 : Nat) :
    writeTape (writeTape tape i v1) i v2 = writeTape tape i v2 := by
  induction tape generalizing i with
  | nil => simp [writeTape]
  | cons d rest ih =>
    cases i with
    | zero => simp [writeTape_cons_zero]
    | succ i' =>
      simp only [writeTape_cons_succ]; congr 1; exact ih i'

private theorem wt_replace_self (tape : List Nat) (i v : Nat) (hlen : i < tape.length) (h : readTape tape i = v) :
    writeTape tape i v = tape := by
  rw [← h]; exact writeTape_read_id tape i hlen

private theorem read_write_self (tape : List Nat) (i v : Nat) :
    readTape (writeTape tape i v) i = v := by
  induction tape generalizing i with
  | nil =>
    simp only [writeTape, List.length_nil, Nat.not_lt_zero, ↓reduceIte, List.nil_append, Nat.sub_zero]
    exact readTape_replicate_append_eq i v
  | cons d rest ih =>
    cases i with
    | zero => simp [writeTape_cons_zero, readTape_cons_zero]
    | succ i' =>
      simp only [writeTape_cons_succ, readTape_cons_succ]
      exact ih i'

private theorem writeTape_length_eq (tape : List Nat) (i v : Nat) (h : i < tape.length) :
    (writeTape tape i v).length = tape.length := by
  simp [writeTape, h, List.length_set]

private theorem rt_split (n : Nat) (d : Nat) (rest : List Nat) :
    readTape (List.replicate n 0 ++ d :: rest) n = d := by
  induction n with
  | zero => simp [readTape, List.getD]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (0 :: List.replicate m 0) ++ d :: rest =
      0 :: (List.replicate m 0 ++ d :: rest) from by simp, readTape_cons_succ]
    exact ih

private theorem wt_split (n : Nat) (d : Nat) (suf : List Nat) (v : Nat) :
    writeTape (List.replicate n 0 ++ d :: suf) n v = List.replicate n 0 ++ v :: suf := by
  induction n with
  | zero => simp [writeTape, List.set]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (0 :: List.replicate m 0) ++ d :: suf =
      0 :: (List.replicate m 0 ++ d :: suf) from by simp, writeTape_cons_succ]
    rw [ih]; simp [List.replicate_succ]

private theorem rep_snoc (n : Nat) :
    List.replicate n 0 ++ [0] = List.replicate (n + 1) 0 := by
  induction n with
  | zero => simp
  | succ m ih => simp [List.replicate_succ]; exact ih

private theorem rt_beyond (tape : List Nat) (pos : Nat) (h : tape.length ≤ pos) :
    readTape tape pos = 0 := by
  induction tape generalizing pos with
  | nil => simp [readTape, List.getD]
  | cons a rest ih =>
    cases pos with
    | zero => simp at h
    | succ p => simp only [readTape_cons_succ]; exact ih p (by simp at h; omega)

private theorem wt_rep_extend (n : Nat) (v : Nat) :
    writeTape (List.replicate n 0) n v = List.replicate n 0 ++ [v] := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ]
    show writeTape (0 :: List.replicate m 0) (m + 1) v = 0 :: (List.replicate m 0 ++ [v])
    rw [writeTape_cons_succ, ih]

-- Bouncing Walkback implementation
theorem walkback_bouncing (tm : TM) (as bs : Nat) (hc : IsClassB tm as bs) :
    ∀ (n : Nat) (d : Nat) (rest : List Nat) (pos : Nat), pos < n →
      (d = 0 ∨ d = 1) →
  ∃ fuel endState, eval tm ⟨as, pos, List.replicate n 0 ++ d :: rest⟩ fuel =
    some ⟨endState, 0, List.replicate n 0 ++ d :: rest⟩ := by
  intro n d rest pos hpos hd
  induction pos with
  | zero =>
    cases n with
    | zero => contradiction
    | succ m =>
      have hz0 : readTape (List.replicate (m + 1) 0 ++ d :: rest) 0 = 0 := by
        exact rt_zeros (m + 1) (d :: rest) 0 (by omega)
      
      have ht_split : List.replicate (m + 1) 0 ++ d :: rest = 0 :: (List.replicate m 0 ++ d :: rest) := by
        rw [List.replicate_succ]; rfl
      
      have hwt0 : writeTape (List.replicate (m + 1) 0 ++ d :: rest) 0 1 = 1 :: (List.replicate m 0 ++ d :: rest) := by
        rw [ht_split]; simp [writeTape]
        
      have hs1 : step tm ⟨as, 0, List.replicate (m + 1) 0 ++ d :: rest⟩ =
          StepResult.continue ⟨bs, 1, 1 :: (List.replicate m 0 ++ d :: rest)⟩ := by
        simp [step, hz0, hc.walk_L, hwt0]
        
      -- Now in bs at pos=1. Tape is 1 :: (List.replicate m 0 ++ d :: rest)
      have hd_read : readTape (1 :: (List.replicate m 0 ++ d :: rest)) 1 = 0 ∨ 
                     readTape (1 :: (List.replicate m 0 ++ d :: rest)) 1 = 1 := by
        rw [readTape_cons_succ]
        cases m with
        | zero => simp [readTape, List.getD]; exact hd
        | succ k => left; exact rt_zeros (k + 1) (d :: rest) 0 (by omega)
        
      rcases hd_read with h_read0 | h_read1
      · -- bs reads 0
        have hwt1 : writeTape (1 :: (List.replicate m 0 ++ d :: rest)) 1 0 = 1 :: (List.replicate m 0 ++ d :: rest) := by
          rw [writeTape_cons_succ]
          exact congrArg (List.cons 1) (writeTape_val_eq_id _ 0 0 (by cases m; simp; simp [List.replicate_succ]) h_read0)
          
        have hs2 : step tm ⟨bs, 1, 1 :: (List.replicate m 0 ++ d :: rest)⟩ =
            StepResult.continue ⟨as, 0, 1 :: (List.replicate m 0 ++ d :: rest)⟩ := by
          simp [step, h_read0, hc.walk_R_0, hwt1]
          
        have hr3 : readTape (1 :: (List.replicate m 0 ++ d :: rest)) 0 = 1 := by rfl
        
        have hwt2 : writeTape (1 :: (List.replicate m 0 ++ d :: rest)) 0 0 = 0 :: (List.replicate m 0 ++ d :: rest) := by simp [writeTape]
        
        have hs3 : step tm ⟨as, 0, 1 :: (List.replicate m 0 ++ d :: rest)⟩ =
            StepResult.halted ⟨as, 0, List.replicate (m + 1) 0 ++ d :: rest⟩ := by
          simp [step, hr3, hc.walk_clr]
          exact ht_split.symm
          
        exact ⟨3, as, by
          rw [eval_step_continue _ _ _ _ hs1]
          rw [eval_step_continue _ _ _ _ hs2]
          rw [eval_step_halt _ _ _ 0 hs3]⟩
          
      · -- bs reads 1
        have hwt1 : writeTape (1 :: (List.replicate m 0 ++ d :: rest)) 1 1 = 1 :: (List.replicate m 0 ++ d :: rest) := by
          rw [writeTape_cons_succ]
          exact congrArg (List.cons 1) (writeTape_val_eq_id _ 0 1 (by cases m; simp; simp [List.replicate_succ]) h_read1)
          
        have hs2 : step tm ⟨bs, 1, 1 :: (List.replicate m 0 ++ d :: rest)⟩ =
            StepResult.continue ⟨as, 0, 1 :: (List.replicate m 0 ++ d :: rest)⟩ := by
          simp [step, h_read1, hc.walk_R_1, hwt1]
          
        have hr3 : readTape (1 :: (List.replicate m 0 ++ d :: rest)) 0 = 1 := by rfl
        
        have hwt2 : writeTape (1 :: (List.replicate m 0 ++ d :: rest)) 0 0 = 0 :: (List.replicate m 0 ++ d :: rest) := by simp [writeTape]
        
        have hs3 : step tm ⟨as, 0, 1 :: (List.replicate m 0 ++ d :: rest)⟩ =
            StepResult.halted ⟨as, 0, List.replicate (m + 1) 0 ++ d :: rest⟩ := by
          simp [step, hr3, hc.walk_clr]
          exact ht_split.symm
          
        exact ⟨3, as, by
          rw [eval_step_continue _ _ _ _ hs1]
          rw [eval_step_continue _ _ _ _ hs2]
          rw [eval_step_halt _ _ _ 0 hs3]⟩
          
  | succ p ih =>
    have hz0 : readTape (List.replicate n 0 ++ d :: rest) (p + 1) = 0 :=
      rt_zeros n (d :: rest) (p + 1) hpos

    let tape1 := writeTape (List.replicate n 0 ++ d :: rest) (p + 1) 1
    have hs1 : step tm ⟨as, p + 1, List.replicate n 0 ++ d :: rest⟩ =
        StepResult.continue ⟨bs, p + 2, tape1⟩ := by
      simp [step, hz0, hc.walk_L]
      
    have hp_neq : (p + 1) ≠ (p + 2) := by omega
    have hr1 : readTape tape1 (p + 2) = readTape (List.replicate n 0 ++ d :: rest) (p + 2) := by
      exact read_write_other _ (p + 1) (p + 2) 1 hp_neq
      
    have hd_read : readTape tape1 (p + 2) = 0 ∨ readTape tape1 (p + 2) = 1 := by
      rw [hr1]
      have hlen : p + 2 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le hlen with heq | hlt
      · rw [heq, rt_split]; exact hd
      · left; exact rt_zeros n (d :: rest) (p + 2) hlt
        
    rcases hd_read with h_read0 | h_read1
    · -- bs reads 0
      have hs2 : step tm ⟨bs, p + 2, tape1⟩ =
          StepResult.continue ⟨as, p + 1, tape1⟩ := by
        simp [step, h_read0, hc.walk_R_0]
        have hw2 : writeTape tape1 (p + 2) 0 = tape1 := by
          have hlen : p + 2 < tape1.length := by
            show p + 2 < (writeTape (List.replicate n 0 ++ d :: rest) (p + 1) 1).length
            rw [writeTape_length_eq _ _ _ (by simp; omega)]; simp; omega
          exact wt_replace_self tape1 (p + 2) 0 hlen h_read0
        rw [hw2]
        
      have hr3 : readTape tape1 (p + 1) = 1 := by
        exact read_write_self _ (p + 1) 1
        
      have hs3 : step tm ⟨as, p + 1, tape1⟩ =
          StepResult.continue ⟨as, p, List.replicate n 0 ++ d :: rest⟩ := by
        have h_rest : writeTape tape1 (p + 1) 0 = List.replicate n 0 ++ d :: rest := by
          change writeTape (writeTape _ _ _) _ _ = _
          rw [write_write_eq]
          exact wt_zeros_id n (d :: rest) (p + 1) hpos
        simp [step, hr3, hc.walk_clr, h_rest]
        
      obtain ⟨f, es, he⟩ := ih (by omega)
      exact ⟨f + 3, es, by
        rw [eval_step_continue _ _ _ _ hs1]
        rw [eval_step_continue _ _ _ _ hs2]
        rw [eval_step_continue _ _ _ _ hs3]
        exact he⟩
        
    · -- bs reads 1
      have hs2 : step tm ⟨bs, p + 2, tape1⟩ =
          StepResult.continue ⟨as, p + 1, tape1⟩ := by
        simp [step, h_read1, hc.walk_R_1]
        have hw2 : writeTape tape1 (p + 2) 1 = tape1 := by
          have hlen : p + 2 < tape1.length := by
            show p + 2 < (writeTape (List.replicate n 0 ++ d :: rest) (p + 1) 1).length
            rw [writeTape_length_eq _ _ _ (by simp; omega)]; simp; omega
          exact wt_replace_self tape1 (p + 2) 1 hlen h_read1
        rw [hw2]
        
      have hr3 : readTape tape1 (p + 1) = 1 := by
        exact read_write_self _ (p + 1) 1
        
      have hs3 : step tm ⟨as, p + 1, tape1⟩ =
          StepResult.continue ⟨as, p, List.replicate n 0 ++ d :: rest⟩ := by
        have h_rest : writeTape tape1 (p + 1) 0 = List.replicate n 0 ++ d :: rest := by
          change writeTape (writeTape _ _ _) _ _ = _
          rw [write_write_eq]
          exact wt_zeros_id n (d :: rest) (p + 1) hpos
        simp [step, hr3, hc.walk_clr, h_rest]
        
      obtain ⟨f, es, he⟩ := ih (by omega)
      exact ⟨f + 3, es, by
        rw [eval_step_continue _ _ _ _ hs1]
        rw [eval_step_continue _ _ _ _ hs2]
        rw [eval_step_continue _ _ _ _ hs3]
        exact he⟩
