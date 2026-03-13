/-
  OneSidedTM.ClassWL — Carry + Left-Absorb + Walking Return
  288 rules from Groups 5 and 6 of the sieve.
-/

import OneSidedTM.Basic
import OneSidedTM.PlusOne

namespace OneSidedTM
open TM

structure IsClassWL (tm : TM) (as : Nat) : Prop where
  carry  : tm.transition 1 1 = { nextState := 1,  write := 0, dir := Dir.L }
  absorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.L }
  walk0  : tm.transition as 0 = { nextState := as, write := 0, dir := Dir.R }
  walk1  : tm.transition as 1 = { nextState := as, write := 1, dir := Dir.R }

-- Walkback: preserves tape while walking R to position 0.
theorem walkback_preserve_WL (tm : TM) (as : Nat)
    (hw0 : tm.transition as 0 = { nextState := as, write := 0, dir := Dir.R })
    (hw1 : tm.transition as 1 = { nextState := as, write := 1, dir := Dir.R })
    (pos : Nat) (tape : List Nat) (hlen : pos < tape.length)
    (hbin : ∀ i, i ≤ pos → readTape tape i = 0 ∨ readTape tape i = 1) :
    eval tm ⟨as, pos, tape⟩ (pos + 1) = some ⟨as, 0, tape⟩ := by
  induction pos with
  | zero =>
    have hs : step tm ⟨as, 0, tape⟩ = StepResult.halted ⟨as, 0, tape⟩ := by
      unfold step
      rcases hbin 0 (Nat.le_refl 0) with h0 | h1
      · simp [h0, hw0, writeTape_val_eq_id tape 0 0 hlen h0]
      · simp [h1, hw1, writeTape_val_eq_id tape 0 1 hlen h1]
    exact eval_step_halt tm _ _ 0 hs
  | succ pos ih =>
    have hsS : step tm ⟨as, pos + 1, tape⟩ = StepResult.continue ⟨as, pos, tape⟩ := by
      unfold step
      rcases hbin (pos + 1) (Nat.le_refl _) with h0 | h1
      · simp [h0, hw0, writeTape_val_eq_id tape (pos + 1) 0 hlen h0]
      · simp [h1, hw1, writeTape_val_eq_id tape (pos + 1) 1 hlen h1]
    rw [show (pos + 1 + 1 : Nat) = pos + 1 + 1 from rfl,
        eval_step_continue tm _ _ _ hsS]
    exact ih (Nat.lt_of_succ_lt hlen) (fun i hi => hbin i (Nat.le_trans hi (Nat.le_succ _)))

-- ============================================================================
-- Helpers
-- ============================================================================

private theorem fromBinary_snoc_zero (xs : List Nat) :
    fromBinary (xs ++ [0]) = fromBinary xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [fromBinary, ih]

-- For the absorb-L case: after absorb at pos n writes 1 and moves to n+1,
-- the walkback at n+1 reads 0 (OOB or rest head is 0), writes 0, moves R.
-- Tape potentially extends by a 0 at position n+1. We need to handle this.
-- Key: if read value = written value, writeTape = id for in-bounds, or tape ++ [0] for OOB-0.

-- Step at position n+1 in 0^n ++ 1 :: rest:
-- Reads rest[0], which is 0 if rest=[] (OOB) or rest head otherwise.
-- Writes same value back. Tape unchanged if in-bounds; extends if OOB.
-- In either case, fromBinary of result = fromBinary of original (trailing 0 invariant).

-- ============================================================================
-- Main simulation
-- ============================================================================

theorem sim_evalWL (tm : TM) (as : Nat)
    (hcarry : tm.transition 1 1 = { nextState := 1, write := 0, dir := Dir.L })
    (habsorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.L })
    (hwalk0 : tm.transition as 0 = { nextState := as, write := 0, dir := Dir.R })
    (hwalk1 : tm.transition as 1 = { nextState := as, write := 1, dir := Dir.R })
    (tape : List Nat)
    (hb : ∀ x ∈ tape, x = 0 ∨ x = 1) :
    ∀ (n : Nat), ∃ (fuel : Nat) (cfg : Config),
      eval tm ⟨1, n, List.replicate n 0 ++ tape⟩ fuel = some cfg ∧
      fromBinary cfg.tape = fromBinary (List.replicate n 0 ++ binarySucc tape) := by
  induction tape with
  | nil =>
    intro n
    -- Tape is 0^n. At pos n, read 0 (OOB). Absorb: write 1, move L to n+1.
    have h_step1 : step tm ⟨1, n, List.replicate n 0⟩ =
        StepResult.continue ⟨as, n + 1, List.replicate n 0 ++ [1]⟩ := by
      simp only [step, rt_beyond _ _ (by simp : n ≥ (List.replicate n 0).length), habsorb,
        wt_rep_extend]
    -- At pos n+1 in 0^n ++ [1], read 0 (OOB). Walk: write 0, move R to n.
    have h_step2 : step tm ⟨as, n + 1, List.replicate n 0 ++ [1]⟩ =
        StepResult.continue ⟨as, n, List.replicate n 0 ++ [1, 0]⟩ := by
      simp only [step, rt_beyond _ _ (by simp : n + 1 ≥ (List.replicate n 0 ++ [1]).length), hwalk0,
        show (n + 1 == 0) = false from by simp]
      simp; unfold writeTape
      simp [show ¬(n + 1 < (List.replicate n 0 ++ [1]).length) from by simp]
    -- Walkback from n to 0 preserves tape
    have hpres := walkback_preserve_WL tm as hwalk0 hwalk1 n
      (List.replicate n 0 ++ [1, 0]) (by simp) (by
        intro i hi
        by_cases h : i < n
        · left; exact rt_zeros _ _ _ h
        · right; rw [show i = n from by omega]; exact rt_split n 1 [0])
    refine ⟨n + 3, ⟨as, 0, List.replicate n 0 ++ [1, 0]⟩, ?_, ?_⟩
    · -- eval chain: 3 steps
      have : List.replicate n 0 ++ ([] : List Nat) = List.replicate n 0 := by simp
      rw [this]
      rw [eval_step_continue _ _ _ _ h_step1, eval_step_continue _ _ _ _ h_step2]
      exact hpres
    · -- fromBinary: 0^n ++ [1,0] = 0^n ++ [1] (trailing 0)
      simp [binarySucc]
      rw [show List.replicate n 0 ++ [1, 0] = (List.replicate n 0 ++ [1]) ++ [0]
        from by simp [List.append_assoc]]
      exact fromBinary_snoc_zero _

  | cons d rest ih =>
    intro n
    have hbd := hb d (List.Mem.head _)
    have hbr : ∀ x ∈ rest, x = 0 ∨ x = 1 := fun x hx => hb x (List.Mem.tail _ hx)
    rcases hbd with rfl | rfl
    · -- d = 0: absorb writes 1 at pos n, moves L to n+1
      have h_rt : readTape (List.replicate n 0 ++ 0 :: rest) n = 0 := rt_split n 0 rest
      have h_absorb : step tm ⟨1, n, List.replicate n 0 ++ 0 :: rest⟩ =
          StepResult.continue ⟨as, n + 1, List.replicate n 0 ++ 1 :: rest⟩ := by
        simp only [step, h_rt, habsorb, wt_split]

      -- Case split on rest for the walkback step at n+1
      cases rest with
      | nil =>
        -- rest = []: tape is 0^n ++ [1], at n+1 reads OOB 0
        have hwA : step tm ⟨as, n + 1, List.replicate n 0 ++ [1]⟩ =
            StepResult.continue ⟨as, n, List.replicate n 0 ++ [1, 0]⟩ := by
          simp only [step, rt_beyond _ _ (by simp : n + 1 ≥ (List.replicate n 0 ++ [1]).length),
            hwalk0, show (n + 1 == 0) = false from by simp]
          simp; unfold writeTape
          simp [show ¬(n + 1 < (List.replicate n 0 ++ [1]).length) from by simp]
        have hpres := walkback_preserve_WL tm as hwalk0 hwalk1 n
          (List.replicate n 0 ++ [1, 0]) (by simp) (by
            intro i hi
            by_cases h : i < n
            · left; exact rt_zeros _ _ _ h
            · right; rw [show i = n from by omega]; exact rt_split n 1 [0])
        exact ⟨n + 3, ⟨as, 0, List.replicate n 0 ++ [1, 0]⟩,
          by rw [eval_step_continue _ _ _ _ h_absorb,
                 eval_step_continue _ _ _ _ hwA]; exact hpres,
          by simp [binarySucc]
             rw [show List.replicate n 0 ++ [1, 0] = (List.replicate n 0 ++ [1]) ++ [0]
               from by simp [List.append_assoc]]; exact fromBinary_snoc_zero _⟩

      | cons r rs =>
        -- rest = r :: rs: tape is 0^n ++ 1 :: r :: rs
        -- At n+1, reads r. Since r ∈ {0,1}, walkback preserves r.
        have hbr_r := hbr r (List.Mem.head _)
        have h_len : n + 1 < (List.replicate n 0 ++ 1 :: r :: rs).length := by simp
        -- Read at n+1: use readTape_append
        have h_rt_r : readTape (List.replicate n 0 ++ 1 :: r :: rs) (n + 1) = r := by
          have : List.replicate n 0 ++ 1 :: r :: rs = (List.replicate n 0 ++ [1]) ++ (r :: rs) := by
            simp [List.append_assoc]
          rw [this]
          have : (List.replicate n 0 ++ [1]).length = n + 1 := by simp
          rw [← this]; rw [readTape_append]; simp [readTape_cons_zero]
        -- Step: writes r back, tape unchanged
        have hwA : step tm ⟨as, n + 1, List.replicate n 0 ++ 1 :: r :: rs⟩ =
            StepResult.continue ⟨as, n, List.replicate n 0 ++ 1 :: r :: rs⟩ := by
          rcases hbr_r with rfl | rfl
          · simp only [step, h_rt_r, hwalk0, show (n + 1 == 0) = false from by simp]
            simp [writeTape_val_eq_id _ _ _ h_len h_rt_r]
          · simp only [step, h_rt_r, hwalk1, show (n + 1 == 0) = false from by simp]
            simp [writeTape_val_eq_id _ _ _ h_len h_rt_r]
        have hpres := walkback_preserve_WL tm as hwalk0 hwalk1 n
          (List.replicate n 0 ++ 1 :: r :: rs) (by simp) (by
            intro i hi
            by_cases h : i < n
            · left; exact rt_zeros _ _ _ h
            · right; rw [show i = n from by omega]; exact rt_split n 1 (r :: rs))
        exact ⟨n + 3, ⟨as, 0, List.replicate n 0 ++ 1 :: r :: rs⟩,
          by rw [eval_step_continue _ _ _ _ h_absorb,
                 eval_step_continue _ _ _ _ hwA]; exact hpres,
          by simp [binarySucc]⟩

    · -- d = 1: carry writes 0, moves L to n+1 → recurse
      have hr := rt_split n 1 rest
      have hc : step tm ⟨1, n, List.replicate n 0 ++ 1 :: rest⟩ =
          StepResult.continue ⟨1, n + 1, List.replicate (n + 1) 0 ++ rest⟩ := by
        simp only [step, hr, hcarry, wt_split]
        congr 1; congr 1
        -- Goal: 0^n ++ 0 :: rest = 0^(n+1) ++ rest
        rw [show List.replicate n 0 ++ 0 :: rest = (List.replicate n 0 ++ [0]) ++ rest
          from by simp [List.append_assoc]]
        rw [rep_snoc]
      obtain ⟨f, cfg, hev, hfb⟩ := ih hbr (n + 1)
      refine ⟨f + 1, cfg, by rw [eval_step_continue _ _ _ _ hc]; exact hev, ?_⟩
      rw [hfb]
      -- fromBinary (0^(n+1) ++ binarySucc rest) = fromBinary (0^n ++ 0 :: binarySucc rest)
      simp only [binarySucc]
      -- 0^(n+1) ++ binarySucc rest = 0^n ++ 0 :: binarySucc rest
      rw [show List.replicate (n + 1) 0 = List.replicate n 0 ++ [0]
        from by rw [← rep_snoc n 0]]; simp [List.append_assoc]

theorem classWL_computesSucc (tm : TM) (as : Nat) (hc : IsClassWL tm as) :
    ComputesSucc tm := by
  intro k _hk
  rcases hc with ⟨hc_carry, hc_absorb, hc_walk0, hc_walk1⟩
  obtain ⟨f, cfg, hev, hfb⟩ := sim_evalWL tm as hc_carry hc_absorb hc_walk0 hc_walk1
    (toBinary k) (toBinary_binary k) 0
  refine ⟨f, ?_⟩
  simp at hev hfb
  simp only [run, initConfig, hev, Option.map]
  simp only [outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary k), fromBinary_toBinary]

end OneSidedTM
