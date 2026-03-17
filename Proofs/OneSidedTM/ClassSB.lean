/-
  OneSidedTM.ClassSB

  Class SB (Scan + Bouncing Clear) one-sided TMs.
  This covers Unknown Groups 3-4 (~120 rules).

  Algorithm:
  1. State 1 scans left past trailing 1-bits (writes 1 = no change)
  2. At first 0 (or past MSB), absorb: write 1, move R, enter clear state `as`
  3. Bouncing Clear: 3-step cycle at each position clears a 1 to 0.
     (as, 1) → (bs, 0, L)  -- Clear 1 to 0, bounce left
     (bs, ?) → (as, ?, R)  -- Bounce right, preserves value
     (as, 0) → (as, 0, R)  -- On cleared 0, advance right (or halt at 0)
-/

import OneSidedTM.Basic
import OneSidedTM.PlusOne
import OneSidedTM.ClassSX

namespace OneSidedTM
open TM

-- ============================================================================
-- Generalized clearback with ∃ fuel
-- ============================================================================

/-- Clearback with variable fuel, binary rest, and non-empty rest. -/
def ValidClearbackV (tm : TM) (as : Nat) : Prop :=
  ∀ (k : Nat) (rest : List Nat), rest.length > 0 →
  (∀ d ∈ rest, d = 0 ∨ d = 1) →
  ∃ fuel endState, eval tm ⟨as, k, List.replicate (k + 1) 1 ++ rest⟩ fuel =
    some ⟨endState, 0, List.replicate (k + 1) 0 ++ rest⟩

-- ============================================================================
-- IsClassSB structure
-- ============================================================================

structure IsClassSB (tm : TM) (as bs : Nat) : Prop where
  skip     : tm.transition 1 1 = { nextState := 1,  write := 1, dir := Dir.L }
  absorb   : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R }
  clear_L  : tm.transition as 1 = { nextState := bs, write := 0, dir := Dir.L }
  clear_R0 : tm.transition bs 0 = { nextState := as, write := 0, dir := Dir.R }
  clear_R1 : tm.transition bs 1 = { nextState := as, write := 1, dir := Dir.R }
  advance  : tm.transition as 0 = { nextState := as, write := 0, dir := Dir.R }

-- ============================================================================
-- Helpers
-- ============================================================================

private theorem rs_ (pre : List Nat) (d : Nat) (suf : List Nat) :
    readTape (pre ++ d :: suf) pre.length = d := by
  induction pre with
  | nil => simp [readTape, List.getD]
  | cons _ rest ih => simp [readTape_cons_succ, ih]

private theorem rl_ (tape : List Nat) : readTape tape tape.length = 0 := by
  induction tape with
  | nil => simp [readTape, List.getD]
  | cons _ rest ih => simp [readTape_cons_succ, ih]

private theorem rep_split (k : Nat) (a : Nat) (rest : List Nat) :
    List.replicate (k + 1) a ++ rest = List.replicate k a ++ (a :: rest) := by
  induction k with
  | zero => simp [List.replicate]
  | succ k ih => simp only [List.replicate_succ, List.cons_append]; exact congrArg (a :: ·) ih

private theorem rt_split_ones (n : Nat) (d : Nat) (rest : List Nat) :
    readTape (List.replicate n 1 ++ d :: rest) n = d := by
  induction n with
  | zero => simp [readTape, List.getD]
  | succ m ih => simp only [List.replicate_succ, List.cons_append, readTape_cons_succ]; exact ih

private theorem readTape_replicate_succ (k : Nat) (rest : List Nat) :
    readTape (List.replicate (k + 2) 1 ++ rest) (k + 1) = 1 := by
  -- 1^(k+2) ++ rest = 1^(k+1) ++ (1 :: rest)
  rw [rep_split (k + 1) 1 rest]
  exact rt_split_ones (k + 1) 1 rest

private theorem writeTape_replicate_succ (k : Nat) (rest : List Nat) :
    writeTape (List.replicate (k + 2) 1 ++ rest) (k + 1) 0 =
    List.replicate (k + 1) 1 ++ (0 :: rest) := by
  induction k generalizing rest with
  | zero => simp [writeTape, List.set, List.replicate]
  | succ k ih =>
    unfold List.replicate
    rw [List.cons_append, writeTape_cons_succ]
    exact congrArg (1 :: ·) (ih rest)

private theorem readTape_binary (tape : List Nat) (pos : Nat)
    (hall : ∀ d ∈ tape, d = 0 ∨ d = 1) :
    readTape tape pos = 0 ∨ readTape tape pos = 1 := by
  induction tape generalizing pos with
  | nil => left; simp [readTape, List.getD]
  | cons d rest ih =>
    cases pos with
    | zero => rw [readTape_cons_zero]; exact hall d (List.mem_cons.mpr (.inl rfl))
    | succ p => rw [readTape_cons_succ]; exact ih p (fun x hx => hall x (List.mem_cons.mpr (.inr hx)))

private theorem ones_eq_rep (l : List Nat) (h : ∀ (d : Nat), d ∈ l → d = 1) :
    l = List.replicate l.length 1 := by
  induction l with
  | nil => rfl
  | cons d rest ih =>
    have hd := h d (List.mem_cons.mpr (.inl rfl))
    subst hd
    exact congrArg (1 :: ·) (ih (fun x hx => h x (List.mem_cons.mpr (.inr hx))))

private theorem replicate_append_one (k : Nat) (a : Nat) :
    List.replicate (k + 1) a = List.replicate k a ++ [a] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show a :: List.replicate (k + 1) a = (a :: List.replicate k a) ++ [a]
    rw [List.cons_append, ih]

private theorem binarySucc_ones_fb (k : Nat) :
    fromBinary (List.replicate k 0 ++ [1]) = fromBinary (binarySucc (List.replicate k 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold List.replicate binarySucc fromBinary
    show 0 + 2 * fromBinary (List.replicate k 0 ++ [1]) =
         0 + 2 * fromBinary (binarySucc (List.replicate k 1))
    rw [ih]

private theorem binarySucc_ones_zero_fb (k : Nat) (rest : List Nat) :
    fromBinary (List.replicate k 0 ++ 1 :: rest) =
    fromBinary (binarySucc (List.replicate k 1 ++ 0 :: rest)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold List.replicate binarySucc fromBinary
    show 0 + 2 * fromBinary (List.replicate k 0 ++ 1 :: rest) =
         0 + 2 * fromBinary (binarySucc (List.replicate k 1 ++ 0 :: rest))
    rw [ih]

-- ============================================================================
-- Bouncing clearback proof
-- ============================================================================

/-- The bouncing clearback clears k+1 ones using a 3-step cycle at each position.
    At position p: (as,1)→(bs,0,L)→(bs,?)→(as,?,R)→(as,0)→(as,0,R).
    Net: cleared tape[p] from 1 to 0, advanced right by 1 position. -/
theorem clearback_bouncing (tm : TM) (as bs : Nat) (hc : IsClassSB tm as bs) :
    ValidClearbackV tm as := by
  intro k rest hrest hbin
  induction k generalizing rest with
  | zero =>
    -- tape = [1] ++ rest
    change ∃ fuel endState, eval tm ⟨as, 0, [1] ++ rest⟩ fuel =
      some ⟨endState, 0, [0] ++ rest⟩
    simp only [List.singleton_append]
    -- Step 1: (as,1) at 0 → (bs,0,L)
    have hs1 : step tm ⟨as, 0, 1 :: rest⟩ =
        StepResult.continue ⟨bs, 1, 0 :: rest⟩ := by
      simp [step, readTape_cons_zero, hc.clear_L, writeTape]
    -- Step 2: bs at 1, reads rest[0] ∈ {0,1}
    have hbin2 : readTape (0 :: rest) 1 = 0 ∨ readTape (0 :: rest) 1 = 1 := by
      rw [readTape_cons_succ]; exact readTape_binary rest 0 hbin
    have hlen1 : 1 < (0 :: rest).length := by simp; omega
    have hs2 : step tm ⟨bs, 1, 0 :: rest⟩ =
        StepResult.continue ⟨as, 0, 0 :: rest⟩ := by
      rcases hbin2 with h0 | h1
      · simp only [step, h0, hc.clear_R0]
        rw [writeTape_val_eq_id _ 1 0 hlen1 h0]; simp [show (1:Nat) ≠ 0 from by omega]
      · simp only [step, h1, hc.clear_R1]
        rw [writeTape_val_eq_id _ 1 1 hlen1 h1]; simp [show (1:Nat) ≠ 0 from by omega]
    -- Step 3: (as,0) at 0 → halt
    have hs3 : step tm ⟨as, 0, 0 :: rest⟩ =
        StepResult.halted ⟨as, 0, 0 :: rest⟩ := by
      simp [step, readTape_cons_zero, hc.advance, writeTape]
    exact ⟨3, as, by
      rw [show (3:Nat) = 2+1 from rfl, eval_step_continue _ _ _ _ hs1,
          show (2:Nat) = 1+1 from rfl, eval_step_continue _ _ _ _ hs2,
          eval_step_halt _ _ _ 0 hs3]⟩

  | succ k ih =>
    -- tape = 1^(k+2) ++ rest, pos = k+1
    have hr := readTape_replicate_succ k rest
    have hwt := writeTape_replicate_succ k rest
    -- Step 1: (as,1) at k+1 → (bs,0,L) → write 0, go to k+2
    have hs1 : step tm ⟨as, k + 1, List.replicate (k + 2) 1 ++ rest⟩ =
        StepResult.continue ⟨bs, k + 2, List.replicate (k + 1) 1 ++ (0 :: rest)⟩ := by
      simp [step, hr, hc.clear_L, hwt]
    -- tape1 = 1^(k+1) ++ (0::rest). All elements binary.
    have hbin_tape1 : ∀ d ∈ (List.replicate (k+1) 1 ++ (0 :: rest)), d = 0 ∨ d = 1 := by
      intro d hd; simp [List.mem_append] at hd
      rcases hd with ⟨_, rfl⟩ | hd
      · exact Or.inr rfl
      · rcases hd with rfl | hd
        · exact Or.inl rfl
        · exact hbin d hd
    -- Step 2: bs at k+2, reads tape1[k+2] ∈ {0,1}
    have hbin_k2 := readTape_binary _ (k+2) hbin_tape1
    have hlen2 : k+2 < (List.replicate (k+1) 1 ++ (0::rest)).length := by simp; omega
    have hs2 : step tm ⟨bs, k+2, List.replicate (k+1) 1 ++ (0::rest)⟩ =
        StepResult.continue ⟨as, k+1, List.replicate (k+1) 1 ++ (0::rest)⟩ := by
      rcases hbin_k2 with h0 | h1
      · simp only [step, h0, hc.clear_R0]
        rw [writeTape_val_eq_id _ (k+2) 0 hlen2 h0]
        simp [show (k+2:Nat) ≠ 0 from by omega, show k+2-1 = k+1 from by omega]
      · simp only [step, h1, hc.clear_R1]
        rw [writeTape_val_eq_id _ (k+2) 1 hlen2 h1]
        simp [show (k+2:Nat) ≠ 0 from by omega, show k+2-1 = k+1 from by omega]
    -- Step 3: (as,0) at k+1. tape1[k+1] = 0 (at the split point of 1^(k+1) ++ 0::rest)
    have hr1 : readTape (List.replicate (k+1) 1 ++ (0::rest)) (k+1) = 0 :=
      rt_split_ones (k+1) 0 rest
    have hlen1 : k + 1 < (List.replicate (k + 1) 1 ++ (0 :: rest)).length := by simp
    have hwt1 := writeTape_val_eq_id _ (k+1) 0 hlen1 hr1
    have hs3 : step tm ⟨as, k+1, List.replicate (k+1) 1 ++ (0::rest)⟩ =
        StepResult.continue ⟨as, k, List.replicate (k+1) 1 ++ (0::rest)⟩ := by
      simp only [step, hr1, hc.advance, Dir.R]
      rw [hwt1]; simp
    -- IH with rest' = 0::rest
    have hbin' : ∀ d ∈ (0::rest), d = 0 ∨ d = 1 := by
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Or.inl rfl
      · exact hbin d hd
    obtain ⟨f, es, he⟩ := ih (0::rest) (by simp) hbin'
    -- 0^(k+2) ++ rest = 0^(k+1) ++ (0::rest)
    have hrep : List.replicate (k + 2) 0 ++ rest =
        List.replicate (k + 1) 0 ++ (0 :: rest) := rep_split (k + 1) 0 rest
    exact ⟨f + 3, es, by
      rw [show k + 1 + 1 = k + 2 from by omega] at hs1
      rw [show f + 3 = ((f + 1) + 1) + 1 from by omega,
          eval_step_continue _ _ _ _ hs1,
          eval_step_continue _ _ _ _ hs2,
          eval_step_continue _ _ _ _ hs3, hrep]; exact he⟩

-- ============================================================================
-- Main theorem: sim_eval for scan + bouncing clear
-- ============================================================================

/-- Adapted sim_eval for scan-based TMs with variable-fuel clearback. -/
theorem sim_eval_SBX (tm : TM) (as : Nat)
    (hskip : tm.transition 1 1 = { nextState := 1, write := 1, dir := Dir.L })
    (habsorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R })
    (hclearback : ValidClearbackV tm as)
    (pre suf : List Nat)
    (hbp : ∀ (d : Nat), d ∈ pre → d = 1)
    (hbs : ∀ (d : Nat), d ∈ suf → d = 0 ∨ d = 1) :
    ∃ fuel cfg, eval tm ⟨1, pre.length, pre ++ suf⟩ fuel = some cfg ∧
    fromBinary cfg.tape = fromBinary (binarySucc (pre ++ suf)) := by
  induction suf generalizing pre with
  | nil =>
    by_cases hp : pre.length = 0
    · have hpnil := List.eq_nil_of_length_eq_zero hp; subst hpnil
      simp only [List.append_nil, binarySucc]
      have hab : step tm ⟨1, 0, []⟩ = StepResult.halted ⟨as, 0, [1]⟩ := by
        unfold step readTape; simp [List.getD, habsorb, writeTape]
      exact ⟨1, _, eval_step_halt tm _ _ 0 hab, rfl⟩
    · simp only [List.append_nil]
      have hrep := ones_eq_rep pre hbp
      have hplen : (pre.length - 1) + 1 = pre.length := by omega
      have hab : step tm ⟨1, pre.length, pre⟩ =
          StepResult.continue ⟨as, pre.length - 1, pre ++ [1]⟩ := by
        simp only [step, rl_ pre, habsorb, Dir.R]
        have : (pre.length == 0) = false := by
          cases pre with | nil => simp at hp | cons _ _ => simp
        rw [this]; simp [writeTape]
      -- clearback on pre ++ [1] = 1^pre.length ++ [1]
      -- pre.length ≥ 1, so k = pre.length - 1, rest = [1]
      obtain ⟨fclear, es, heval_clear⟩ := hclearback (pre.length - 1) [1] (by simp) (by simp)
      have heval : eval tm ⟨1, pre.length, pre⟩ (fclear + 1) =
          some ⟨es, 0, List.replicate pre.length 0 ++ [1]⟩ := by
        rw [eval_step_continue tm _ _ _ hab, hrep]
        simp only [List.length_replicate]; rw [← hplen]; exact heval_clear
      exact ⟨_, _, heval, by
        rw [hrep]; simp only [List.length_replicate]
        exact binarySucc_ones_fb pre.length⟩

  | cons d rest ih =>
    have hbr : ∀ (x : Nat), x ∈ rest → x = 0 ∨ x = 1 :=
      fun x hx => hbs x (List.mem_cons.mpr (.inr hx))
    rcases hbs d (List.mem_cons.mpr (.inl rfl)) with rfl | rfl
    · by_cases hp : pre.length = 0
      · have hpnil := List.eq_nil_of_length_eq_zero hp; subst hpnil; simp
        have hab : step tm ⟨1, 0, 0 :: rest⟩ = StepResult.halted ⟨as, 0, 1 :: rest⟩ := by
          unfold step readTape; simp [List.getD, habsorb, writeTape]
        exact ⟨1, _, eval_step_halt tm _ _ 0 hab, by simp [binarySucc]⟩
      · have hrep := ones_eq_rep pre hbp
        have hplen : (pre.length - 1) + 1 = pre.length := by omega
        have hab : step tm ⟨1, pre.length, pre ++ 0 :: rest⟩ =
            StepResult.continue ⟨as, pre.length - 1, pre ++ 1 :: rest⟩ := by
          simp only [step, rs_ pre 0 rest, habsorb, Dir.R]
          have : (pre.length == 0) = false := by
            cases pre with | nil => simp at hp | cons _ _ => simp
          rw [this]; simp [writeTape_append pre 0 rest 1]
        -- clearback on pre ++ [1] ++ rest = 1^pre.length ++ (1::rest)
        -- k = pre.length - 1, rest' = 1::rest
        have hbin_rest' : ∀ d ∈ (1 :: rest), d = 0 ∨ d = 1 := by
          intro x hx; simp at hx; rcases hx with rfl | hx
          · exact Or.inr rfl
          · exact hbr x hx
        obtain ⟨fclear, es, heval_clear⟩ :=
          hclearback (pre.length - 1) (1 :: rest) (by simp) hbin_rest'
        have heval : eval tm ⟨1, pre.length, pre ++ 0 :: rest⟩ (fclear + 1) =
            some ⟨es, 0, List.replicate pre.length 0 ++ 1 :: rest⟩ := by
          rw [eval_step_continue tm _ _ _ hab, hrep]
          simp only [List.length_replicate]; rw [← hplen]; exact heval_clear
        exact ⟨_, _, heval, by
          rw [hrep]; simp only [List.length_replicate]
          exact binarySucc_ones_zero_fb pre.length rest⟩

    · have hbp' : ∀ (x : Nat), x ∈ pre ++ [1] → x = 1 := by
        intro x hx; simp at hx; rcases hx with h | h; exact hbp x h; exact h
      obtain ⟨f, c, he, hf⟩ := ih (pre ++ [1]) hbp' hbr
      have hskipS : step tm ⟨1, pre.length, pre ++ 1 :: rest⟩ =
          StepResult.continue ⟨1, pre.length + 1, pre ++ 1 :: rest⟩ := by
        simp only [step, rs_ pre 1 rest, hskip]
        have hwt := writeTape_val_eq_id (pre ++ 1 :: rest) pre.length 1
          (by simp) (rs_ pre 1 rest)
        simp [Dir.L, hwt]
      exact ⟨_, _, by
        rw [eval_step_continue tm _ _ f hskipS,
            show pre.length + 1 = (pre ++ [1]).length from by simp,
            show pre ++ 1 :: rest = (pre ++ [1]) ++ rest from by simp]; exact he,
        by rw [show pre ++ 1 :: rest = (pre ++ [1]) ++ rest from by simp]; exact hf⟩

-- ============================================================================
-- ComputesSucc for Class SB
-- ============================================================================

theorem classSB_computesSucc (tm : TM) (as bs : Nat) (hc : IsClassSB tm as bs) :
    ComputesSucc tm := by
  intro n _hn
  obtain ⟨fuel, cfg, heval, hfb⟩ :=
    sim_eval_SBX tm as hc.skip hc.absorb (clearback_bouncing tm as bs hc) [] (toBinary n)
      (fun _ h => nomatch h) (toBinary_binary n)
  refine ⟨fuel, ?_⟩; simp at heval hfb
  simp only [run, initConfig, heval, Option.map, outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

end OneSidedTM
