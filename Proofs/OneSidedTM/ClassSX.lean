/-
  OneSidedTM.ClassSX

  Extended Class S (Scan-MSB) proofs covering ALL clear-back variants:
  self-loop, toggle, and drop.

  Algorithm (same as ClassS):
  1. State 1 scans left past trailing 1-bits (writes 1 = no change)
  2. At first 0 (or MSB), absorb: write 1, move R, enter state `as`
  3. Clear phase: walk right zeroing each 1-bit until halt at position 0

  The clear phase can use:
  - Self-loop: (as, 1) → {as, 0, R}
  - Toggle: (as, 1) → {bs, 0, R}, (bs, 1) → {as, 0, R}
  - Drop: (as, 1) → {bs, 0, R}, (bs, 1) → {bs, 0, R}
-/

import OneSidedTM.Basic
import OneSidedTM.PlusOne

namespace OneSidedTM
open TM

-- ============================================================================
-- Valid clearback abstraction
-- ============================================================================

/-- A clearback predicate: starting from state `as` at position `k`
    over a tape `List.replicate (k+1) 1 ++ rest`, it eventually halts
    at position 0 with tape `List.replicate (k+1) 0 ++ rest`. -/
def ValidClearback (tm : TM) (as : Nat) : Prop :=
  ∀ (k : Nat) (rest : List Nat),
  eval tm ⟨as, k, List.replicate (k + 1) 1 ++ rest⟩ (k + 1) =
    some ⟨as, 0, List.replicate (k + 1) 0 ++ rest⟩

-- Wait, the final state may not be `as` for toggle/drop variants!
-- For self-loop: always halts in `as`
-- For toggle: halts in as or bs depending on parity of k
-- For drop: halts in bs (if k >= 1) or bs (if k = 0)
-- But `outputValue` only cares about the tape, not the state!
-- So I should generalize: exists some endState.

/-- Generalized clearback: clears k+1 ones starting at position k,
    halting at position 0 with some state. -/
def ValidClearbackG (tm : TM) (as : Nat) : Prop :=
  ∀ (k : Nat) (rest : List Nat),
  ∃ endState, eval tm ⟨as, k, List.replicate (k + 1) 1 ++ rest⟩ (k + 1) =
    some ⟨endState, 0, List.replicate (k + 1) 0 ++ rest⟩

-- ============================================================================
-- Helper lemmas
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

private theorem replicate_append_one (k : Nat) (a : Nat) :
    List.replicate (k + 1) a = List.replicate k a ++ [a] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show a :: List.replicate (k + 1) a = (a :: List.replicate k a) ++ [a]
    rw [List.cons_append, ih]

private theorem readTape_replicate_succ (k : Nat) (rest : List Nat) :
    readTape (List.replicate (k + 2) 1 ++ rest) (k + 1) = 1 := by
  induction k generalizing rest with
  | zero => simp [List.replicate, readTape, readTape_cons_succ, List.getD]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, readTape_cons_succ]
    exact ih rest

private theorem writeTape_replicate_succ (k : Nat) (rest : List Nat) :
    writeTape (List.replicate (k + 2) 1 ++ rest) (k + 1) 0 =
    List.replicate (k + 1) 1 ++ (0 :: rest) := by
  induction k generalizing rest with
  | zero => simp [writeTape, List.replicate]
  | succ k ih =>
    unfold List.replicate
    rw [List.cons_append, writeTape_cons_succ]
    exact congrArg (1 :: ·) (ih rest)

private theorem ones_eq_rep (l : List Nat) (h : ∀ (d : Nat), d ∈ l → d = 1) :
    l = List.replicate l.length 1 := by
  induction l with
  | nil => rfl
  | cons d rest ih =>
    have hd := h d (List.mem_cons.mpr (.inl rfl))
    subst hd
    exact congrArg (1 :: ·) (ih (fun x hx => h x (List.mem_cons.mpr (.inr hx))))

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
-- Clearback proofs for 3 variants
-- ============================================================================

-- Self-loop clearback
theorem clearback_self (tm : TM) (as : Nat)
    (hclear : tm.transition as 1 = { nextState := as, write := 0, dir := Dir.R }) :
    ValidClearbackG tm as := by
  intro k rest
  induction k generalizing rest with
  | zero =>
    have hs : step tm ⟨as, 0, 1 :: rest⟩ = StepResult.halted ⟨as, 0, 0 :: rest⟩ := by
      unfold step readTape; simp [List.getD, hclear, writeTape]
    exact ⟨as, eval_step_halt tm _ _ 0 hs⟩
  | succ k ih =>
    have hr := readTape_replicate_succ k rest
    have hwt := writeTape_replicate_succ k rest
    have hs : step tm ⟨as, k + 1, List.replicate (k + 2) 1 ++ rest⟩ =
        StepResult.continue ⟨as, k, List.replicate (k + 1) 1 ++ 0 :: rest⟩ := by
      simp only [step, hr, hclear, hwt]; simp
    obtain ⟨es, he⟩ := ih (0 :: rest)
    exact ⟨es, by
      rw [show (k + 1 + 1 : Nat) = (k + 1) + 1 from by omega,
          eval_step_continue tm _ _ (k + 1) hs,
          replicate_append_one (k + 1) 0, List.append_assoc]
      simp; exact he⟩

-- Toggle clearback
theorem clearback_toggle (tm : TM) (as bs : Nat)
    (hclearA : tm.transition as 1 = { nextState := bs, write := 0, dir := Dir.R })
    (hclearB : tm.transition bs 1 = { nextState := as, write := 0, dir := Dir.R }) :
    ValidClearbackG tm as ∧ ValidClearbackG tm bs := by
  have H : ∀ k rest, ∀ s, (s = as ∨ s = bs) →
      ∃ endState, eval tm ⟨s, k, List.replicate (k + 1) 1 ++ rest⟩ (k + 1) =
        some ⟨endState, 0, List.replicate (k + 1) 0 ++ rest⟩ := by
    intro k
    induction k with
    | zero =>
      intro rest s hs
      rcases hs with hA | hB
      · have hsS : step tm ⟨s, 0, 1 :: rest⟩ = StepResult.halted ⟨bs, 0, 0 :: rest⟩ := by
          unfold step readTape; simp [List.getD, hA, hclearA, writeTape]
        exact ⟨bs, eval_step_halt tm _ _ 0 hsS⟩
      · have hsS : step tm ⟨s, 0, 1 :: rest⟩ = StepResult.halted ⟨as, 0, 0 :: rest⟩ := by
          unfold step readTape; simp [List.getD, hB, hclearB, writeTape]
        exact ⟨as, eval_step_halt tm _ _ 0 hsS⟩
    | succ k ih =>
      intro rest s hs
      have hr := readTape_replicate_succ k rest
      have hwt := writeTape_replicate_succ k rest
      rcases hs with hA | hB
      · have hsS : step tm ⟨s, k + 1, List.replicate (k + 2) 1 ++ rest⟩ =
            StepResult.continue ⟨bs, k, List.replicate (k + 1) 1 ++ 0 :: rest⟩ := by
          simp only [step, hr, hA, hclearA, hwt]; simp
        obtain ⟨es, he⟩ := ih (0 :: rest) bs (Or.inr rfl)
        exact ⟨es, by
          rw [show (k + 1 + 1 : Nat) = (k + 1) + 1 from by omega,
              eval_step_continue tm _ _ (k + 1) hsS,
              replicate_append_one (k + 1) 0, List.append_assoc]
          simp; exact he⟩
      · have hsS : step tm ⟨s, k + 1, List.replicate (k + 2) 1 ++ rest⟩ =
            StepResult.continue ⟨as, k, List.replicate (k + 1) 1 ++ 0 :: rest⟩ := by
          simp only [step, hr, hB, hclearB, hwt]; simp
        obtain ⟨es, he⟩ := ih (0 :: rest) as (Or.inl rfl)
        exact ⟨es, by
          rw [show (k + 1 + 1 : Nat) = (k + 1) + 1 from by omega,
              eval_step_continue tm _ _ (k + 1) hsS,
              replicate_append_one (k + 1) 0, List.append_assoc]
          simp; exact he⟩
  exact ⟨fun k rest => H k rest as (Or.inl rfl),
         fun k rest => H k rest bs (Or.inr rfl)⟩

-- Drop clearback
private theorem clearback_drop_bs (tm : TM) (bs : Nat)
    (hclear : tm.transition bs 1 = { nextState := bs, write := 0, dir := Dir.R }) :
    ValidClearbackG tm bs :=
  clearback_self tm bs hclear

theorem clearback_drop (tm : TM) (as bs : Nat)
    (hclearA : tm.transition as 1 = { nextState := bs, write := 0, dir := Dir.R })
    (hclearB : tm.transition bs 1 = { nextState := bs, write := 0, dir := Dir.R }) :
    ValidClearbackG tm as := by
  intro k rest
  cases k with
  | zero =>
    have hs : step tm ⟨as, 0, 1 :: rest⟩ = StepResult.halted ⟨bs, 0, 0 :: rest⟩ := by
      unfold step readTape; simp [List.getD, hclearA, writeTape]
    exact ⟨bs, eval_step_halt tm _ _ 0 hs⟩
  | succ k =>
    have hr := readTape_replicate_succ k rest
    have hwt := writeTape_replicate_succ k rest
    have hsS : step tm ⟨as, k + 1, List.replicate (k + 2) 1 ++ rest⟩ =
        StepResult.continue ⟨bs, k, List.replicate (k + 1) 1 ++ 0 :: rest⟩ := by
      simp only [step, hr, hclearA, hwt]; simp
    obtain ⟨es, he⟩ := clearback_drop_bs tm bs hclearB k (0 :: rest)
    exact ⟨es, by
      rw [show (k + 1 + 1 : Nat) = (k + 1) + 1 from by omega,
          eval_step_continue tm _ _ (k + 1) hsS,
          replicate_append_one (k + 1) 0, List.append_assoc]
      simp; exact he⟩

-- ============================================================================
-- Core simulation: parameterized by ValidClearbackG
-- ============================================================================

theorem sim_eval_SX (tm : TM) (as : Nat)
    (hskip : tm.transition 1 1 = { nextState := 1, write := 1, dir := Dir.L })
    (habsorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R })
    (hclearback : ValidClearbackG tm as)
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
      obtain ⟨es, heval_clear⟩ := hclearback (pre.length - 1) [1]
      have heval : eval tm ⟨1, pre.length, pre⟩ (pre.length + 1) =
          some ⟨es, 0, List.replicate pre.length 0 ++ [1]⟩ := by
        rw [eval_step_continue tm _ _ _ hab, hrep]
        simp only [List.length_replicate]; rw [← hplen]
        exact heval_clear
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
        obtain ⟨es, heval_clear⟩ := hclearback (pre.length - 1) (1 :: rest)
        have heval : eval tm ⟨1, pre.length, pre ++ 0 :: rest⟩ (pre.length + 1) =
            some ⟨es, 0, List.replicate pre.length 0 ++ 1 :: rest⟩ := by
          rw [eval_step_continue tm _ _ _ hab, hrep]
          simp only [List.length_replicate]
          rw [← hplen]
          exact heval_clear
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
-- ComputesSucc theorems
-- ============================================================================

/-- Any TM with skip + absorb + self-loop clear computes successor -/
theorem classSX_self_computes (tm : TM) (as : Nat)
    (hskip : tm.transition 1 1 = { nextState := 1, write := 1, dir := Dir.L })
    (habsorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R })
    (hclear : tm.transition as 1 = { nextState := as, write := 0, dir := Dir.R }) :
    ComputesSucc tm := by
  intro n _hn
  obtain ⟨fuel, cfg, heval, hfb⟩ :=
    sim_eval_SX tm as hskip habsorb (clearback_self tm as hclear) [] (toBinary n)
      (fun _ h => nomatch h) (toBinary_binary n)
  refine ⟨fuel, ?_⟩; simp at heval hfb
  simp only [run, initConfig, heval, Option.map, outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

/-- Any TM with skip + absorb + toggle clear computes successor -/
theorem classSX_toggle_computes (tm : TM) (as bs : Nat)
    (hskip : tm.transition 1 1 = { nextState := 1, write := 1, dir := Dir.L })
    (habsorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R })
    (hclearA : tm.transition as 1 = { nextState := bs, write := 0, dir := Dir.R })
    (hclearB : tm.transition bs 1 = { nextState := as, write := 0, dir := Dir.R }) :
    ComputesSucc tm := by
  intro n _hn
  obtain ⟨fuel, cfg, heval, hfb⟩ :=
    sim_eval_SX tm as hskip habsorb (clearback_toggle tm as bs hclearA hclearB).1 [] (toBinary n)
      (fun _ h => nomatch h) (toBinary_binary n)
  refine ⟨fuel, ?_⟩; simp at heval hfb
  simp only [run, initConfig, heval, Option.map, outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

/-- Any TM with skip + absorb + drop clear computes successor -/
theorem classSX_drop_computes (tm : TM) (as bs : Nat)
    (hskip : tm.transition 1 1 = { nextState := 1, write := 1, dir := Dir.L })
    (habsorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R })
    (hclearA : tm.transition as 1 = { nextState := bs, write := 0, dir := Dir.R })
    (hclearB : tm.transition bs 1 = { nextState := bs, write := 0, dir := Dir.R }) :
    ComputesSucc tm := by
  intro n _hn
  obtain ⟨fuel, cfg, heval, hfb⟩ :=
    sim_eval_SX tm as hskip habsorb (clearback_drop tm as bs hclearA hclearB) [] (toBinary n)
      (fun _ h => nomatch h) (toBinary_binary n)
  refine ⟨fuel, ?_⟩; simp at heval hfb
  simp only [run, initConfig, heval, Option.map, outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

-- ============================================================================
-- Concrete Implementations
-- ============================================================================

-- Group 3 Toggle: as=2, bs=3
def exampleSX3Toggle : TM where
  numStates := 3; numSymbols := 2
  transition := fun s sy => match s, sy with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 1, dir := Dir.L }
    | 2, 1 => { nextState := 3, write := 0, dir := Dir.R }
    | 3, 1 => { nextState := 2, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.R }

theorem exampleSX3Toggle_computesSucc : ComputesSucc exampleSX3Toggle :=
  classSX_toggle_computes exampleSX3Toggle 2 3 rfl rfl rfl rfl

-- Group 3 Drop: as=2, bs=3
def exampleSX3Drop : TM where
  numStates := 3; numSymbols := 2
  transition := fun s sy => match s, sy with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 1, dir := Dir.L }
    | 2, 1 => { nextState := 3, write := 0, dir := Dir.R }
    | 3, 1 => { nextState := 3, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.R }

theorem exampleSX3Drop_computesSucc : ComputesSucc exampleSX3Drop :=
  classSX_drop_computes exampleSX3Drop 2 3 rfl rfl rfl rfl

-- Group 4 Toggle: as=3, bs=2
def exampleSX4Toggle : TM where
  numStates := 3; numSymbols := 2
  transition := fun s sy => match s, sy with
    | 1, 0 => { nextState := 3, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 1, dir := Dir.L }
    | 3, 1 => { nextState := 2, write := 0, dir := Dir.R }
    | 2, 1 => { nextState := 3, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.R }

theorem exampleSX4Toggle_computesSucc : ComputesSucc exampleSX4Toggle :=
  classSX_toggle_computes exampleSX4Toggle 3 2 rfl rfl rfl rfl

-- Group 4 Drop: as=3, bs=2
def exampleSX4Drop : TM where
  numStates := 3; numSymbols := 2
  transition := fun s sy => match s, sy with
    | 1, 0 => { nextState := 3, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 1, dir := Dir.L }
    | 3, 1 => { nextState := 2, write := 0, dir := Dir.R }
    | 2, 1 => { nextState := 2, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.R }

theorem exampleSX4Drop_computesSucc : ComputesSucc exampleSX4Drop :=
  classSX_drop_computes exampleSX4Drop 3 2 rfl rfl rfl rfl

-- ============================================================================
-- Generalized scan eval with parametric scan state cs
-- ============================================================================

/-- Like sim_eval_SX but with scan state cs instead of hardcoded 1.
    Enables scan delegation proofs where state 1 delegates to cs.
    cs scans past 1s (writing 1 = no change), absorbs at first 0, then clearback. -/
theorem sim_eval_scan (tm : TM) (cs as : Nat)
    (hskip : tm.transition cs 1 = { nextState := cs, write := 1, dir := Dir.L })
    (habsorb : tm.transition cs 0 = { nextState := as, write := 1, dir := Dir.R })
    (hclearback : ValidClearbackG tm as)
    (pre suf : List Nat)
    (hbp : ∀ (d : Nat), d ∈ pre → d = 1)
    (hbs : ∀ (d : Nat), d ∈ suf → d = 0 ∨ d = 1) :
    ∃ fuel cfg, eval tm ⟨cs, pre.length, pre ++ suf⟩ fuel = some cfg ∧
    fromBinary cfg.tape = fromBinary (binarySucc (pre ++ suf)) := by
  -- Proof mirrors sim_eval_SX with cs replacing 1
  induction suf generalizing pre with
  | nil =>
    by_cases hp : pre.length = 0
    · have hpnil := List.eq_nil_of_length_eq_zero hp; subst hpnil
      simp only [List.append_nil, binarySucc]
      have hab : step tm ⟨cs, 0, []⟩ = StepResult.halted ⟨as, 0, [1]⟩ := by
        unfold step readTape; simp [List.getD, habsorb, writeTape]
      exact ⟨1, _, eval_step_halt tm _ _ 0 hab, rfl⟩
    · simp only [List.append_nil]
      have hrep := ones_eq_rep pre hbp
      have hplen : (pre.length - 1) + 1 = pre.length := by omega
      have hab : step tm ⟨cs, pre.length, pre⟩ =
          StepResult.continue ⟨as, pre.length - 1, pre ++ [1]⟩ := by
        simp only [step, rl_ pre, habsorb, Dir.R]
        have : (pre.length == 0) = false := by
          cases pre with | nil => simp at hp | cons _ _ => simp
        rw [this]; simp [writeTape]
      obtain ⟨es, heval_clear⟩ := hclearback (pre.length - 1) [1]
      have heval : eval tm ⟨cs, pre.length, pre⟩ (pre.length + 1) =
          some ⟨es, 0, List.replicate pre.length 0 ++ [1]⟩ := by
        rw [eval_step_continue tm _ _ _ hab, hrep]
        simp only [List.length_replicate]; rw [← hplen]
        exact heval_clear
      exact ⟨_, _, heval, by
        rw [hrep]; simp only [List.length_replicate]
        exact binarySucc_ones_fb pre.length⟩

  | cons d rest ih =>
    have hbr : ∀ (x : Nat), x ∈ rest → x = 0 ∨ x = 1 :=
      fun x hx => hbs x (List.mem_cons.mpr (.inr hx))
    rcases hbs d (List.mem_cons.mpr (.inl rfl)) with rfl | rfl
    · by_cases hp : pre.length = 0
      · have hpnil := List.eq_nil_of_length_eq_zero hp; subst hpnil; simp
        have hab : step tm ⟨cs, 0, 0 :: rest⟩ = StepResult.halted ⟨as, 0, 1 :: rest⟩ := by
          unfold step readTape; simp [List.getD, habsorb, writeTape]
        exact ⟨1, _, eval_step_halt tm _ _ 0 hab, by simp [binarySucc]⟩
      · have hrep := ones_eq_rep pre hbp
        have hplen : (pre.length - 1) + 1 = pre.length := by omega
        have hab : step tm ⟨cs, pre.length, pre ++ 0 :: rest⟩ =
            StepResult.continue ⟨as, pre.length - 1, pre ++ 1 :: rest⟩ := by
          simp only [step, rs_ pre 0 rest, habsorb, Dir.R]
          have : (pre.length == 0) = false := by
            cases pre with | nil => simp at hp | cons _ _ => simp
          rw [this]; simp [writeTape_append pre 0 rest 1]
        obtain ⟨es, heval_clear⟩ := hclearback (pre.length - 1) (1 :: rest)
        have heval : eval tm ⟨cs, pre.length, pre ++ 0 :: rest⟩ (pre.length + 1) =
            some ⟨es, 0, List.replicate pre.length 0 ++ 1 :: rest⟩ := by
          rw [eval_step_continue tm _ _ _ hab, hrep]
          simp only [List.length_replicate]
          rw [← hplen]
          exact heval_clear
        exact ⟨_, _, heval, by
          rw [hrep]; simp only [List.length_replicate]
          exact binarySucc_ones_zero_fb pre.length rest⟩

    · have hbp' : ∀ (x : Nat), x ∈ pre ++ [1] → x = 1 := by
        intro x hx; simp at hx; rcases hx with h | h; exact hbp x h; exact h
      obtain ⟨f, c, he, hf⟩ := ih (pre ++ [1]) hbp' hbr
      have hskipS : step tm ⟨cs, pre.length, pre ++ 1 :: rest⟩ =
          StepResult.continue ⟨cs, pre.length + 1, pre ++ 1 :: rest⟩ := by
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
-- Scan delegation wrapper: first scan step from state 1, rest from cs
-- ============================================================================

/-- Scan delegation: state 1 delegates scan to cs on first 1 encounter.
    After one step, cs continues scanning via sim_eval_scan. -/
theorem sim_eval_scan_delegate (tm : TM) (cs as : Nat)
    (habsorb1 : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R })
    (hdelegate : tm.transition 1 1 = { nextState := cs, write := 1, dir := Dir.L })
    (hskip_cs : tm.transition cs 1 = { nextState := cs, write := 1, dir := Dir.L })
    (habsorb_cs : tm.transition cs 0 = { nextState := as, write := 1, dir := Dir.R })
    (hclearback : ValidClearbackG tm as)
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
        unfold step readTape; simp [List.getD, habsorb1, writeTape]
      exact ⟨1, _, eval_step_halt tm _ _ 0 hab, rfl⟩
    · simp only [List.append_nil]
      have hrep := ones_eq_rep pre hbp
      have hplen : (pre.length - 1) + 1 = pre.length := by omega
      have hab : step tm ⟨1, pre.length, pre⟩ =
          StepResult.continue ⟨as, pre.length - 1, pre ++ [1]⟩ := by
        simp only [step, rl_ pre, habsorb1, Dir.R]
        have : (pre.length == 0) = false := by
          cases pre with | nil => simp at hp | cons _ _ => simp
        rw [this]; simp [writeTape]
      obtain ⟨es, heval_clear⟩ := hclearback (pre.length - 1) [1]
      have heval : eval tm ⟨1, pre.length, pre⟩ (pre.length + 1) =
          some ⟨es, 0, List.replicate pre.length 0 ++ [1]⟩ := by
        rw [eval_step_continue tm _ _ _ hab, hrep]
        simp only [List.length_replicate]; rw [← hplen]
        exact heval_clear
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
          unfold step readTape; simp [List.getD, habsorb1, writeTape]
        exact ⟨1, _, eval_step_halt tm _ _ 0 hab, by simp [binarySucc]⟩
      · have hrep := ones_eq_rep pre hbp
        have hplen : (pre.length - 1) + 1 = pre.length := by omega
        have hab : step tm ⟨1, pre.length, pre ++ 0 :: rest⟩ =
            StepResult.continue ⟨as, pre.length - 1, pre ++ 1 :: rest⟩ := by
          simp only [step, rs_ pre 0 rest, habsorb1, Dir.R]
          have : (pre.length == 0) = false := by
            cases pre with | nil => simp at hp | cons _ _ => simp
          rw [this]; simp [writeTape_append pre 0 rest 1]
        obtain ⟨es, heval_clear⟩ := hclearback (pre.length - 1) (1 :: rest)
        have heval : eval tm ⟨1, pre.length, pre ++ 0 :: rest⟩ (pre.length + 1) =
            some ⟨es, 0, List.replicate pre.length 0 ++ 1 :: rest⟩ := by
          rw [eval_step_continue tm _ _ _ hab, hrep]
          simp only [List.length_replicate]; rw [← hplen]
          exact heval_clear
        exact ⟨_, _, heval, by
          rw [hrep]; simp only [List.length_replicate]
          exact binarySucc_ones_zero_fb pre.length rest⟩
    · -- d = 1: state 1 DELEGATES to cs
      have hbp' : ∀ (x : Nat), x ∈ pre ++ [1] → x = 1 := by
        intro x hx; simp at hx; rcases hx with h | h; exact hbp x h; exact h
      have hskipS : step tm ⟨1, pre.length, pre ++ 1 :: rest⟩ =
          StepResult.continue ⟨cs, pre.length + 1, pre ++ 1 :: rest⟩ := by
        simp only [step, rs_ pre 1 rest, hdelegate]
        have hwt := writeTape_val_eq_id (pre ++ 1 :: rest) pre.length 1
          (by simp) (rs_ pre 1 rest)
        simp [Dir.L, hwt]
      obtain ⟨f, c, he, hf⟩ := sim_eval_scan tm cs as hskip_cs habsorb_cs hclearback
        (pre ++ [1]) rest hbp' hbr
      exact ⟨_, _, by
        rw [eval_step_continue tm _ _ f hskipS,
            show pre.length + 1 = (pre ++ [1]).length from by simp,
            show pre ++ 1 :: rest = (pre ++ [1]) ++ rest from by simp]; exact he,
        by rw [show pre ++ 1 :: rest = (pre ++ [1]) ++ rest from by simp]; exact hf⟩

-- ============================================================================
-- Rule-numbered instances via fromRuleNumber32
-- ============================================================================

theorem r658573_succ : ComputesSucc (fromRuleNumber32 658573) :=
  classSX_toggle_computes (fromRuleNumber32 658573) 2 3 rfl rfl rfl rfl

theorem r658621_succ : ComputesSucc (fromRuleNumber32 658621) :=
  classSX_drop_computes (fromRuleNumber32 658621) 2 3 rfl rfl rfl rfl

theorem r741517_succ : ComputesSucc (fromRuleNumber32 741517) :=
  classSX_toggle_computes (fromRuleNumber32 741517) 3 2 rfl rfl rfl rfl

theorem r734605_succ : ComputesSucc (fromRuleNumber32 734605) :=
  classSX_drop_computes (fromRuleNumber32 734605) 3 2 rfl rfl rfl rfl

end OneSidedTM
