/-
  OneSidedTM.ThreeState

  Rule 146514 (3-state, 2-symbol) — the dominant genuine 3-state successor algorithm.
  2,352 rules share this step profile, making it the most common true 3-state pattern.

  Transition table:
    (1,0) → {2, 1, R}   -- absorb: write 1, move R
    (1,1) → {1, 0, L}   -- carry: flip 1→0, move L
    (2,0) → {3, 0, R}   -- walk-back A: move R
    (2,1) → {1, 0, L}   -- (unused during +1)
    (3,0) → {2, 0, R}   -- walk-back B: move R
    (3,1) → {2, 0, R}   -- (unused during +1)
-/

import OneSidedTM.PlusOne

namespace OneSidedTM
open TM

-- ============================================================================
-- Rule definition
-- ============================================================================

def rule146514 : TM where
  numStates := 3
  numSymbols := 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.R }
    | 1, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 2, 0 => { nextState := 3, write := 0, dir := Dir.R }
    | 2, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 3, 0 => { nextState := 2, write := 0, dir := Dir.R }
    | 3, 1 => { nextState := 2, write := 0, dir := Dir.R }
    | _, _ => { nextState := 1, write := 0, dir := Dir.R }

-- Bulk verification
theorem r146514_bulk : ∀ n ∈ List.range 4096,
    n = 0 ∨ run rule146514 n 200 = some (n + 1) := by native_decide

-- ============================================================================
-- Step lemmas (proven by unfolding step/rule146514)
-- ============================================================================

private theorem carry_s (tape : List Nat) (pos : Nat) (h : readTape tape pos = 1) :
    step rule146514 ⟨1, pos, tape⟩ =
    StepResult.continue ⟨1, pos + 1, writeTape tape pos 0⟩ := by
  simp only [step, h, rule146514]

private theorem absorb_s (tape : List Nat) (pos : Nat) (h : readTape tape pos = 0)
    (hp : pos > 0) :
    step rule146514 ⟨1, pos, tape⟩ =
    StepResult.continue ⟨2, pos - 1, writeTape tape pos 1⟩ := by
  simp only [step, h, rule146514]
  have : (pos == 0) = false := by cases pos with | zero => omega | succ _ => rfl
  rw [this]; rfl

private theorem absorb_halt_s (tape : List Nat) (h : readTape tape 0 = 0) :
    step rule146514 ⟨1, 0, tape⟩ =
    StepResult.halted ⟨2, 0, writeTape tape 0 1⟩ := by
  simp only [step, h, rule146514]; rfl

-- Walk step: state 2 or 3, reading 0, pos > 0, flips state, writes 0
private theorem walk2_s (tape : List Nat) (pos : Nat) (h : readTape tape pos = 0) (hp : pos > 0) :
    step rule146514 ⟨2, pos, tape⟩ =
    StepResult.continue ⟨3, pos - 1, writeTape tape pos 0⟩ := by
  simp only [step, h, rule146514]
  have : (pos == 0) = false := by cases pos with | zero => omega | succ _ => rfl
  rw [this]; rfl

private theorem walk3_s (tape : List Nat) (pos : Nat) (h : readTape tape pos = 0) (hp : pos > 0) :
    step rule146514 ⟨3, pos, tape⟩ =
    StepResult.continue ⟨2, pos - 1, writeTape tape pos 0⟩ := by
  simp only [step, h, rule146514]
  have : (pos == 0) = false := by cases pos with | zero => omega | succ _ => rfl
  rw [this]; rfl

-- Walk halt: state 2 or 3, reading 0, pos = 0
private theorem walk2_halt (tape : List Nat) (h : readTape tape 0 = 0) :
    step rule146514 ⟨2, 0, tape⟩ =
    StepResult.halted ⟨3, 0, writeTape tape 0 0⟩ := by
  simp only [step, h, rule146514]; rfl

private theorem walk3_halt (tape : List Nat) (h : readTape tape 0 = 0) :
    step rule146514 ⟨3, 0, tape⟩ =
    StepResult.halted ⟨2, 0, writeTape tape 0 0⟩ := by
  simp only [step, h, rule146514]; rfl

-- Tape helpers: use rt_zeros, rt_split, rt_beyond, wt_split, rep_snoc,
-- wt_rep_extend from Basic.lean (imported via OneSidedTM.Basic)
-- ============================================================================
-- Walk-back: single-step induction on position, tracking state {2,3}
-- ============================================================================

/-- Walk-back from state s ∈ {2,3} at position pos through all-zero prefix.
    Tape is preserved. Halts when reaching position 0. -/
private theorem walkback (n : Nat) (suf : List Nat) (pos : Nat) (s : Nat)
    (hs : s = 2 ∨ s = 3) (hpos : pos < n) :
    ∃ fuel cfg, eval rule146514 ⟨s, pos, List.replicate n 0 ++ suf⟩ fuel = some cfg ∧
    cfg.tape = List.replicate n 0 ++ suf := by
  induction pos generalizing s with
  | zero =>
    have h0 := rt_zeros n suf 0 (by omega)
    have hwt : writeTape (List.replicate n 0 ++ suf) 0 0 = List.replicate n 0 ++ suf :=
      writeTape_val_eq_id _ 0 0 (by simp; omega) h0
    rcases hs with rfl | rfl
    · exact ⟨1, ⟨3, 0, writeTape (List.replicate n 0 ++ suf) 0 0⟩,
        by simp [eval, walk2_halt _ h0], by rw [hwt]⟩
    · exact ⟨1, ⟨2, 0, writeTape (List.replicate n 0 ++ suf) 0 0⟩,
        by simp [eval, walk3_halt _ h0], by rw [hwt]⟩
  | succ p ih =>
    have hz := rt_zeros n suf (p + 1) (by omega)
    have hwt : writeTape (List.replicate n 0 ++ suf) (p + 1) 0 = List.replicate n 0 ++ suf :=
      writeTape_val_eq_id _ (p + 1) 0 (by simp; omega) hz
    -- One step: state s at p+1 → state (flip s) at p, tape unchanged after writeTape
    rcases hs with rfl | rfl
    · -- state 2 at p+1 → state 3 at p
      obtain ⟨f, c, hf, hc⟩ := ih 3 (Or.inr rfl) (by omega)
      exact ⟨f + 1, c,
        by rw [eval_step_continue _ _ _ _ (walk2_s _ (p + 1) hz (by omega)), hwt,
               show p + 1 - 1 = p from by omega]; exact hf,
        hc⟩
    · -- state 3 at p+1 → state 2 at p
      obtain ⟨f, c, hf, hc⟩ := ih 2 (Or.inl rfl) (by omega)
      exact ⟨f + 1, c,
        by rw [eval_step_continue _ _ _ _ (walk3_s _ (p + 1) hz (by omega)), hwt,
               show p + 1 - 1 = p from by omega]; exact hf,
        hc⟩

-- ============================================================================
-- Core simulation
-- ============================================================================

/-- Core: from state 1 at position n on tape (replicate n 0 ++ suf),
    produces successor value. The all-zeros prefix invariant is maintained
    by the carry phase (flips 1→0). -/
theorem sim_eval146 (n : Nat) (suf : List Nat)
    (hbs : ∀ d ∈ suf, d = 0 ∨ d = 1) :
    ∃ fuel cfg, eval rule146514 ⟨1, n, List.replicate n 0 ++ suf⟩ fuel = some cfg ∧
    fromBinary cfg.tape = fromBinary (List.replicate n 0 ++ binarySucc suf) := by
  induction suf generalizing n with
  | nil =>
    -- suffix = []: absorb at MSB extends tape, walk back
    simp only [List.append_nil, binarySucc]
    cases n with
    | zero =>
      exact ⟨1, ⟨2, 0, [1]⟩,
        by simp [eval, absorb_halt_s [] (by simp [readTape, List.getD]),
                 writeTape, List.set],
        by simp [fromBinary]⟩
    | succ m =>
      have hr := rt_beyond (List.replicate (m + 1) 0) (m + 1) (by simp)
      have hwt := wt_rep_extend (m + 1) 1
      have ha : step rule146514 ⟨1, m + 1, List.replicate (m + 1) 0⟩ =
          StepResult.continue ⟨2, m, List.replicate (m + 1) 0 ++ [1]⟩ := by
        rw [absorb_s _ _ hr (by omega), hwt]; simp
      obtain ⟨fw, cw, hw, htw⟩ := walkback (m + 1) [1] m 2 (Or.inl rfl) (by omega)
      exact ⟨fw + 1, cw,
        by rw [eval_step_continue _ _ _ _ ha]; exact hw,
        by rw [htw]⟩
  | cons d rest ih =>
    have hbr : ∀ x ∈ rest, x = 0 ∨ x = 1 :=
      fun x hx => hbs x (List.mem_cons.mpr (.inr hx))
    rcases hbs d (List.mem_cons.mpr (.inl rfl)) with rfl | rfl
    · -- d = 0: absorb → walk back
      simp only [binarySucc]
      cases n with
      | zero =>
        exact ⟨1, ⟨2, 0, 1 :: rest⟩,
          by simp [eval, absorb_halt_s (0 :: rest) (by simp [readTape, List.getD]),
                   writeTape, List.set],
          by simp [fromBinary]⟩
      | succ m =>
        have hr := rt_split (m + 1) 0 rest
        have ha : step rule146514 ⟨1, m + 1, List.replicate (m + 1) 0 ++ 0 :: rest⟩ =
            StepResult.continue ⟨2, m, List.replicate (m + 1) 0 ++ 1 :: rest⟩ := by
          rw [absorb_s _ _ hr (by omega), wt_split]; simp
        obtain ⟨fw, cw, hw, htw⟩ := walkback (m + 1) (1 :: rest) m 2 (Or.inl rfl) (by omega)
        exact ⟨fw + 1, cw,
          by rw [eval_step_continue _ _ _ _ ha]; exact hw,
          by rw [htw]⟩
    · -- d = 1: carry → recurse with prefix extended by one zero
      have hrd : readTape (List.replicate n 0 ++ 1 :: rest) n = 1 := rt_split n 1 rest
      have ha : step rule146514 ⟨1, n, List.replicate n 0 ++ 1 :: rest⟩ =
          StepResult.continue ⟨1, n + 1, List.replicate (n + 1) 0 ++ rest⟩ := by
        rw [carry_s _ _ hrd, wt_split]
        show StepResult.continue ⟨1, n + 1, List.replicate n 0 ++ 0 :: rest⟩ =
          StepResult.continue ⟨1, n + 1, List.replicate (n + 1) 0 ++ rest⟩
        congr 1; rw [← rep_snoc]; simp
      obtain ⟨f, c, he, hf⟩ := ih (n + 1) hbr
      exact ⟨f + 1, c,
        by rw [eval_step_continue _ _ _ _ ha]; exact he,
        by rw [hf]; congr 1;
           show List.replicate (n + 1) 0 ++ binarySucc rest =
             List.replicate n 0 ++ 0 :: binarySucc rest;
           rw [← rep_snoc, List.append_assoc]; rfl⟩

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- Rule 146514 computes successor for all n ≥ 1.
    Formally verified GENUINE 3-state TM for binary successor.
    The proof has infinite leverage: proves correctness for ALL inputs. -/
theorem rule146514_computesSucc : ComputesSucc rule146514 := by
  intro n _hn
  obtain ⟨fuel, cfg, heval, hfb⟩ :=
    sim_eval146 0 (toBinary n) (toBinary_binary n)
  refine ⟨fuel, ?_⟩
  simp at heval hfb
  simp only [run, initConfig, heval, Option.map]
  simp only [outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

end OneSidedTM
