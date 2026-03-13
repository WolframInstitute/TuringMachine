/-
  OneSidedTM.PlusOne

  Definition of TM rule 445 and proof that it computes successor.

  Rule 445 ({2,2} TM):
    (1, 0) → (2, 1, L)   -- carry absorbed
    (1, 1) → (1, 0, L)   -- carry propagate
    (2, 0) → (2, 0, R)   -- scan-back
    (2, 1) → (2, 1, R)   -- scan-back

  Head starts at position 0 (LSB).
-/

import OneSidedTM.Basic

namespace OneSidedTM
open TM

-- ============================================================================
-- Rule 445 definition
-- ============================================================================

def rule445 : TM where
  numStates := 2
  numSymbols := 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.L }
    | 1, 1 => { nextState := 1, write := 0, dir := Dir.L }
    | 2, 0 => { nextState := 2, write := 0, dir := Dir.R }
    | 2, 1 => { nextState := 2, write := 1, dir := Dir.R }
    | _, _ => { nextState := 2, write := 0, dir := Dir.R }

-- ============================================================================
-- Machine-checked proofs for specific inputs
-- ============================================================================

-- Individual spot checks
theorem rule445_succ_1 : run rule445 1 10 = some 2 := by native_decide
theorem rule445_succ_2 : run rule445 2 10 = some 3 := by native_decide
theorem rule445_succ_3 : run rule445 3 10 = some 4 := by native_decide
theorem rule445_succ_4 : run rule445 4 10 = some 5 := by native_decide
theorem rule445_succ_5 : run rule445 5 10 = some 6 := by native_decide
theorem rule445_succ_6 : run rule445 6 10 = some 7 := by native_decide
theorem rule445_succ_7 : run rule445 7 20 = some 8 := by native_decide
theorem rule445_succ_8 : run rule445 8 20 = some 9 := by native_decide
theorem rule445_succ_15 : run rule445 15 40 = some 16 := by native_decide
theorem rule445_succ_16 : run rule445 16 40 = some 17 := by native_decide
theorem rule445_succ_31 : run rule445 31 40 = some 32 := by native_decide
theorem rule445_succ_63 : run rule445 63 40 = some 64 := by native_decide
theorem rule445_succ_100 : run rule445 100 200 = some 101 := by native_decide
theorem rule445_succ_127 : run rule445 127 200 = some 128 := by native_decide
theorem rule445_succ_255 : run rule445 255 200 = some 256 := by native_decide
theorem rule445_succ_256 : run rule445 256 200 = some 257 := by native_decide
theorem rule445_succ_511 : run rule445 511 200 = some 512 := by native_decide
theorem rule445_succ_1000 : run rule445 1000 200 = some 1001 := by native_decide
theorem rule445_succ_1023 : run rule445 1023 200 = some 1024 := by native_decide

-- Bulk verification: all inputs 1..65535
theorem rule445_succ_bulk : ∀ n ∈ List.range 65536,
    n = 0 ∨ run rule445 n 200 = some (n + 1) := by native_decide

-- ============================================================================
-- Binary digit list operations
-- ============================================================================

def binarySucc : List Nat → List Nat
  | [] => [1]
  | 0 :: rest => 1 :: rest
  | 1 :: rest => 0 :: binarySucc rest
  | _ :: rest => 1 :: rest

theorem fromBinary_binarySucc (l : List Nat)
    (h_bin : ∀ d ∈ l, d = 0 ∨ d = 1) :
    fromBinary (binarySucc l) = fromBinary l + 1 := by
  induction l with
  | nil => simp [binarySucc, fromBinary]
  | cons d rest ih =>
    match d with
    | 0 => simp [binarySucc, fromBinary]; omega
    | 1 =>
      simp [binarySucc, fromBinary]
      have h_rest : ∀ d ∈ rest, d = 0 ∨ d = 1 := by
        intro d hd; exact h_bin d (List.mem_cons_of_mem _ hd)
      have := ih h_rest; omega
    | d + 2 =>
      exfalso; have := h_bin (d + 2) (List.mem_cons_self _ _); omega

theorem toBinary_binary (n : Nat) : ∀ d ∈ toBinary n, d = 0 ∨ d = 1 := by
  unfold toBinary
  split
  · intro d hd; simp [List.mem_singleton] at hd; left; exact hd
  · intro d hd; exact toBinaryPos_binary _ d hd
where
  toBinaryPos_binary : (n : Nat) → ∀ d ∈ toBinary.toBinaryPos n, d = 0 ∨ d = 1
    | 0 => by intro d hd; simp [toBinary.toBinaryPos] at hd
    | n + 1 => by
      intro d hd
      unfold toBinary.toBinaryPos at hd; simp at hd
      cases hd with
      | inl h => have := Nat.mod_lt (n + 1) (by omega : 2 > 0); omega
      | inr h => exact toBinaryPos_binary ((n + 1) / 2) d h
  termination_by n => n

-- ============================================================================
-- toBinary_succ: the key encoding lemma
-- ============================================================================

private theorem toBinaryPos_succ (n : Nat) (hn : n ≥ 1) :
    toBinary.toBinaryPos (n + 1) = binarySucc (toBinary.toBinaryPos n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, hn with
    | 1, _ => simp [toBinary.toBinaryPos, binarySucc]
    | n' + 2, _ =>
      unfold toBinary.toBinaryPos; simp
      by_cases heven : (n' + 2) % 2 = 0
      · rw [show (n' + 3) % 2 = 1 from by omega, heven]
        simp [binarySucc]
        rw [show (n' + 3) / 2 = (n' + 2) / 2 from by omega]
      · rw [show (n' + 3) % 2 = 0 from by omega, show (n' + 2) % 2 = 1 from by omega]
        simp [binarySucc]
        rw [show (n' + 3) / 2 = (n' + 2) / 2 + 1 from by omega]
        exact ih ((n' + 2) / 2) (Nat.div_lt_self (by omega) (by omega)) (by omega)

theorem toBinary_succ (n : Nat) :
    toBinary (n + 1) = binarySucc (toBinary n) := by
  match n with
  | 0 => simp [toBinary, toBinary.toBinaryPos, binarySucc]
  | 1 => simp [toBinary, toBinary.toBinaryPos, binarySucc]
  | n' + 2 => simp only [toBinary]; exact toBinaryPos_succ (n' + 2) (by omega)

-- ============================================================================
-- eval composition lemmas
-- ============================================================================

theorem eval_step_continue (tm : TM) (cfg cfg' : Config) (fuel : Nat)
    (h : step tm cfg = StepResult.continue cfg') :
    eval tm cfg (fuel + 1) = eval tm cfg' fuel := by
  simp [eval, h]

theorem eval_step_halt (tm : TM) (cfg cfg' : Config) (fuel : Nat)
    (h : step tm cfg = StepResult.halted cfg') :
    eval tm cfg (fuel + 1) = some cfg' := by
  simp [eval, h]

-- ============================================================================
-- TM phase simulation lemmas (all fully proved)
-- ============================================================================

theorem carry_step (tape : List Nat) (pos : Nat)
    (h : readTape tape pos = 1) :
    step rule445 ⟨1, pos, tape⟩ =
    StepResult.continue ⟨1, pos + 1, writeTape tape pos 0⟩ := by
  simp only [step, h, rule445]

theorem absorb_step (tape : List Nat) (pos : Nat)
    (h : readTape tape pos = 0) :
    step rule445 ⟨1, pos, tape⟩ =
    StepResult.continue ⟨2, pos + 1, writeTape tape pos 1⟩ := by
  simp only [step, h, rule445]

theorem scanback_step_0 (tape : List Nat) (pos : Nat)
    (hpos : pos > 0) (h : readTape tape pos = 0) :
    step rule445 ⟨2, pos, tape⟩ =
    StepResult.continue ⟨2, pos - 1, writeTape tape pos 0⟩ := by
  simp only [step, h, rule445, Dir.R]
  have : (pos == 0) = false := by cases pos with | zero => omega | succ _ => rfl
  rw [this]; simp [StepResult.continue]

theorem scanback_step_1 (tape : List Nat) (pos : Nat)
    (hpos : pos > 0) (h : readTape tape pos = 1) :
    step rule445 ⟨2, pos, tape⟩ =
    StepResult.continue ⟨2, pos - 1, writeTape tape pos 1⟩ := by
  simp only [step, h, rule445, Dir.R]
  have hbeq : (pos == 0) = false := by cases pos with | zero => omega | succ _ => rfl
  rw [hbeq]; simp [StepResult.continue]

theorem halt_step_0 (tape : List Nat) (h : readTape tape 0 = 0) :
    step rule445 ⟨2, 0, tape⟩ = StepResult.halted ⟨2, 0, writeTape tape 0 0⟩ := by
  simp only [step, h, rule445]; rfl

theorem halt_step_1 (tape : List Nat) (h : readTape tape 0 = 1) :
    step rule445 ⟨2, 0, tape⟩ = StepResult.halted ⟨2, 0, writeTape tape 0 1⟩ := by
  simp only [step, h, rule445]; rfl

-- ============================================================================
-- readTape / writeTape simplification lemmas
-- ============================================================================
-- Scan-back phase: state 2 preserves tape (writes back what it reads)
-- ============================================================================

-- ============================================================================
-- Scan-back phase: state 2 preserves tape (writes back what it reads)
-- ============================================================================

theorem halt_step_id (tape : List Nat) (hlen : 0 < tape.length)
    (hbin : readTape tape 0 = 0 ∨ readTape tape 0 = 1) :
    step rule445 ⟨2, 0, tape⟩ = StepResult.halted ⟨2, 0, tape⟩ := by
  cases hbin with
  | inl h0 =>
    rw [halt_step_0 tape h0,
        show writeTape tape 0 0 = tape from writeTape_val_eq_id tape 0 0 hlen h0]
  | inr h1 =>
    rw [halt_step_1 tape h1,
        show writeTape tape 0 1 = tape from writeTape_val_eq_id tape 0 1 hlen h1]

theorem scanback_step_id (tape : List Nat) (pos : Nat)
    (hpos : pos > 0) (hlen : pos < tape.length)
    (hbin : readTape tape pos = 0 ∨ readTape tape pos = 1) :
    step rule445 ⟨2, pos, tape⟩ = StepResult.continue ⟨2, pos - 1, tape⟩ := by
  cases hbin with
  | inl h0 =>
    rw [scanback_step_0 tape pos hpos h0,
        show writeTape tape pos 0 = tape from writeTape_val_eq_id tape pos 0 hlen h0]
  | inr h1 =>
    rw [scanback_step_1 tape pos hpos h1,
        show writeTape tape pos 1 = tape from writeTape_val_eq_id tape pos 1 hlen h1]

theorem scanback_eval (tape : List Nat) (p : Nat) (hlen : p < tape.length)
    (hbin : ∀ i, i ≤ p → i < tape.length → readTape tape i = 0 ∨ readTape tape i = 1) :
    eval rule445 ⟨2, p, tape⟩ (p + 1) = some ⟨2, 0, tape⟩ := by
  induction p with
  | zero =>
    exact eval_step_halt rule445 _ _ 0 (halt_step_id tape hlen (hbin 0 (by omega) hlen))
  | succ p ih =>
    rw [show (p + 1 + 1 : Nat) = (p + 1) + 1 from by omega,
        eval_step_continue rule445 _ _ (p + 1)
          (scanback_step_id tape (p + 1) (by omega) hlen (hbin (p+1) (by omega) hlen))]
    simp; exact ih (by omega) (fun i hi hil => hbin i (by omega) hil)

-- ============================================================================
-- fromBinary is invariant under trailing zeros
-- ============================================================================

theorem fromBinary_append_zero (l : List Nat) :
    fromBinary (l ++ [0]) = fromBinary l := by
  induction l with
  | nil => simp [fromBinary]
  | cons d rest ih => simp [fromBinary, ih]

theorem fromBinary_append_all_zero (l suffix : List Nat) (h : ∀ x ∈ suffix, x = 0) :
    fromBinary (l ++ suffix) = fromBinary l := by
  induction suffix generalizing l with
  | nil => simp
  | cons d rest ih =>
    have hd : d = 0 := h d (List.mem_cons_self _ _)
    rw [show l ++ d :: rest = (l ++ [d]) ++ rest from by simp]
    rw [ih (l ++ [d]) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rw [hd, fromBinary_append_zero]

private theorem List.pred_of_mem_takeWhile' {α : Type} {p : α → Bool} {l : List α} {x : α}
    (hx : x ∈ l.takeWhile p) : p x = true := by
  induction l with
  | nil => simp [List.takeWhile] at hx
  | cons a rest ih =>
    simp only [List.takeWhile] at hx; split at hx
    · rename_i hp; simp at hx; cases hx with
      | inl heq => subst heq; exact hp
      | inr hmem => exact ih hmem
    · simp at hx

/-- trimTrailingZeros preserves fromBinary value.
    Removing high-order zeros doesn't change a binary number's value. -/
theorem fromBinary_trim (l : List Nat) :
    fromBinary (trimTrailingZeros l) = fromBinary l := by
  cases l with
  | nil => simp [trimTrailingZeros, fromBinary]
  | cons a rest =>
    show fromBinary (let r := (a :: rest).reverse.dropWhile (· == 0)
      if r.isEmpty then [0] else r.reverse) = fromBinary (a :: rest)
    generalize hdw : (a :: rest).reverse.dropWhile (· == 0) = dw
    generalize htw : (a :: rest).reverse.takeWhile (· == 0) = tw
    have hl_eq : (a :: rest) = dw.reverse ++ tw.reverse := by
      have h1 := (List.takeWhile_append_dropWhile (· == 0) (a :: rest).reverse).symm
      rw [htw, hdw] at h1
      have h2 := congrArg List.reverse h1
      simp only [List.reverse_append, List.reverse_reverse] at h2
      exact h2
    have htw_zero : ∀ x ∈ tw.reverse, x = 0 := by
      intro x hx; rw [List.mem_reverse] at hx; rw [← htw] at hx
      have hp := List.pred_of_mem_takeWhile' hx; simp at hp; exact hp
    have hfb : fromBinary (a :: rest) = fromBinary dw.reverse := by
      rw [hl_eq]; exact fromBinary_append_all_zero dw.reverse tw.reverse htw_zero
    simp only
    split
    · rename_i hempty
      simp only [fromBinary]
      have : fromBinary (a :: rest) = 0 := by
        rw [hfb, List.isEmpty_eq_true.mp hempty]; simp [fromBinary]
      simp [fromBinary] at this; omega
    · exact hfb.symm

-- ============================================================================
-- Step count
-- eval_mono is now defined in Basic.lean

-- Helper to convert from the Basic.lean form to the ≤ form used here
private theorem eval_mono' (tm : TM) (cfg r : Config) (fuel fuel' : Nat) :
    eval tm cfg fuel = some r → fuel ≤ fuel' → eval tm cfg fuel' = some r := by
  intro h hle
  have : fuel' = fuel + (fuel' - fuel) := by omega
  rw [this]
  exact eval_mono tm cfg fuel (fuel' - fuel) r h

-- ============================================================================
-- readTape / writeTape at prefix boundary
-- ============================================================================

theorem readTape_append (l1 l2 : List Nat) :
    readTape (l1 ++ l2) l1.length = readTape l2 0 := by
  induction l1 with
  | nil => simp
  | cons d rest ih => simp [readTape_cons_succ, ih]

theorem writeTape_append (l1 : List Nat) (d : Nat) (l2 : List Nat) (v : Nat) :
    writeTape (l1 ++ d :: l2) l1.length v = l1 ++ v :: l2 := by
  induction l1 with
  | nil => simp [writeTape_cons_zero]
  | cons a rest ih => simp [writeTape_cons_succ, ih]

-- ============================================================================
-- Simulation assembly helpers
-- ============================================================================

-- readTape at end of list returns 0
private theorem readTape_at_length (tape : List Nat) : readTape tape tape.length = 0 := by
  induction tape with
  | nil => simp [readTape, List.getD]
  | cons d rest ih => simp [readTape_cons_succ, ih]

-- readTape at |prefix| in prefix ++ d :: suffix = d
private theorem readTape_at_split (pre : List Nat) (d : Nat) (suf : List Nat) :
    readTape (pre ++ d :: suf) pre.length = d := by
  induction pre with
  | nil => simp [readTape, List.getD]
  | cons a rest ih => simp [readTape_cons_succ, ih]

-- readTape returns 0 or 1 on binary tape
private theorem readTape_binary (tape : List Nat) (pos : Nat)
    (hbin : ∀ d ∈ tape, d = 0 ∨ d = 1) :
    readTape tape pos = 0 ∨ readTape tape pos = 1 := by
  induction tape generalizing pos with
  | nil => left; simp [readTape, List.getD]
  | cons d rest ih =>
    cases pos with
    | zero => 
      rw [readTape_cons_zero]
      exact hbin d (List.mem_cons_self _ _)
    | succ p =>
      rw [readTape_cons_succ]
      exact ih p (fun x hx => hbin x (List.mem_cons_of_mem _ hx))

-- Step wrappers: absorb at end of tape (out of bounds)
private theorem absorb_end_step (pre : List Nat) :
    step rule445 ⟨1, pre.length, pre⟩ =
    StepResult.continue ⟨2, pre.length + 1, pre ++ [1]⟩ := by
  rw [absorb_step _ _ (readTape_at_length pre)]; simp [writeTape]

-- Step wrappers: absorb at position within tape (suffix starts with 0)
private theorem absorb_pos_step (pre suf : List Nat) :
    step rule445 ⟨1, pre.length, pre ++ 0 :: suf⟩ =
    StepResult.continue ⟨2, pre.length + 1, pre ++ 1 :: suf⟩ := by
  rw [absorb_step _ _ (readTape_at_split pre 0 suf)]
  simp [writeTape_append pre 0 suf 1]

-- Step wrappers: carry at position (suffix starts with 1)
private theorem carry_pos_step (pre suf : List Nat) :
    step rule445 ⟨1, pre.length, pre ++ 1 :: suf⟩ =
    StepResult.continue ⟨1, pre.length + 1, pre ++ 0 :: suf⟩ := by
  rw [carry_step _ _ (readTape_at_split pre 1 suf)]
  simp [writeTape_append pre 1 suf 0]

-- Step wrappers: scanback extension (head beyond tape, extends tape)
private theorem scanback_ext_step (pre : List Nat) :
    step rule445 ⟨2, pre.length + 1, pre ++ [1]⟩ =
    StepResult.continue ⟨2, pre.length, pre ++ [1, 0]⟩ := by
  have hr : readTape (pre ++ [1]) (pre.length + 1) = 0 := by
    rw [show pre.length + 1 = (pre ++ [1]).length from by simp]
    exact readTape_at_length _
  simp only [scanback_step_0 _ _ (by omega) hr, Nat.add_sub_cancel]
  simp [writeTape]

-- Binary tape membership: pre ++ [1, 0] is binary if pre is
private theorem bin_tape_10 (pre : List Nat) (h : ∀ d ∈ pre, d = 0 ∨ d = 1) :
    ∀ d ∈ (pre ++ [1, 0] : List Nat), d = 0 ∨ d = 1 := by
  intro d hd; simp at hd
  cases hd with
  | inl h' => exact h d h'
  | inr h' => cases h' with
    | inl h' => right; exact h'
    | inr h' => left; exact h'

-- Binary tape membership: pre ++ 1 :: rest is binary if pre and rest are
private theorem bin_tape_1r (pre rest : List Nat) (hp : ∀ d ∈ pre, d = 0 ∨ d = 1)
    (hr : ∀ d ∈ rest, d = 0 ∨ d = 1) :
    ∀ d ∈ (pre ++ 1 :: rest : List Nat), d = 0 ∨ d = 1 := by
  intro d hd; simp at hd
  cases hd with
  | inl h => exact hp d h
  | inr h => cases h with
    | inl h => right; exact h
    | inr h => exact hr d h

-- fromBinary (pre ++ [1, 0]) = fromBinary (pre ++ [1])
private theorem fromBinary_ext_zero (pre : List Nat) :
    fromBinary (pre ++ [1, 0]) = fromBinary (pre ++ [1]) := by
  rw [show pre ++ [1, 0] = (pre ++ [1]) ++ [0] from by simp]
  exact fromBinary_append_zero _

-- ============================================================================
-- Core simulation lemma
-- ============================================================================

/-- For binary prefix `pre` and suffix `suf`, evaluating rule445 from state 1
    at position |pre| on tape `pre ++ suf` produces a config whose fromBinary
    equals `fromBinary (pre ++ binarySucc suf)`.
    This is the key inductive lemma that decomposes the TM execution into
    carry, absorb, and scanback phases. -/
theorem sim_eval (pre suf : List Nat)
    (hbp : ∀ d ∈ pre, d = 0 ∨ d = 1) (hbs : ∀ d ∈ suf, d = 0 ∨ d = 1) :
    ∃ fuel cfg, eval rule445 ⟨1, pre.length, pre ++ suf⟩ fuel = some cfg ∧
    fromBinary cfg.tape = fromBinary (pre ++ binarySucc suf) := by
  induction suf generalizing pre with
  | nil =>
    -- suffix = []: absorb at end → extension → scanback
    have heval : eval rule445 ⟨1, pre.length, pre⟩ (pre.length + 3) =
        some ⟨2, 0, pre ++ [1, 0]⟩ := by
      rw [show pre.length + 3 = ((pre.length + 1) + 1) + 1 from by omega,
          eval_step_continue rule445 _ _ _ (absorb_end_step pre),
          eval_step_continue rule445 _ _ _ (scanback_ext_step pre)]
      exact scanback_eval _ pre.length (by simp)
        (fun i _ _ => readTape_binary _ _ (bin_tape_10 pre hbp))
    simp only [List.append_nil]
    exact ⟨_, _, heval, fromBinary_ext_zero pre⟩

  | cons d rest ih =>
    have hbr : ∀ x ∈ rest, x = 0 ∨ x = 1 :=
      fun x hx => hbs x (List.mem_cons_of_mem _ hx)
    rcases hbs d (List.mem_cons_self _ _) with rfl | rfl
    · -- d = 0, suffix = 0 :: rest
      by_cases hrest : rest = []
      · -- suffix = [0]: absorb + extension + scanback
        subst hrest
        have heval : eval rule445 ⟨1, pre.length, pre ++ [0]⟩ (pre.length + 3) =
            some ⟨2, 0, pre ++ [1, 0]⟩ := by
          rw [show pre.length + 3 = ((pre.length + 1) + 1) + 1 from by omega,
              eval_step_continue rule445 _ _ _ (absorb_pos_step pre []),
              eval_step_continue rule445 _ _ _ (scanback_ext_step pre)]
          exact scanback_eval _ pre.length (by simp)
            (fun i _ _ => readTape_binary _ _ (bin_tape_10 pre hbp))
        exact ⟨_, _, heval, fromBinary_ext_zero pre⟩
      · -- suffix = 0 :: rest with rest ≠ []: absorb + direct scanback
        have hlen : pre.length + 1 < (pre ++ 1 :: rest).length := by
          simp; exact Nat.pos_of_ne_zero
            (by intro h; exact hrest (List.length_eq_zero.mp h))
        have heval : eval rule445 ⟨1, pre.length, pre ++ 0 :: rest⟩ (pre.length + 3) =
            some ⟨2, 0, pre ++ 1 :: rest⟩ := by
          rw [show pre.length + 3 = (pre.length + 2) + 1 from by omega,
              eval_step_continue rule445 _ _ _ (absorb_pos_step pre rest)]
          exact scanback_eval _ _ hlen
            (fun i _ _ => readTape_binary _ _ (bin_tape_1r pre rest hbp hbr))
        exact ⟨_, _, heval, rfl⟩

    · -- d = 1, suffix = 1 :: rest: carry + inductive hypothesis
      have hbp' : ∀ x ∈ pre ++ [0], x = 0 ∨ x = 1 := by
        intro x hx; simp at hx
        cases hx with
        | inl h => exact hbp x h
        | inr h => left; exact h
      obtain ⟨f, c, he, hf⟩ := ih (pre ++ [0]) hbp' hbr
      have heval : eval rule445 ⟨1, pre.length, pre ++ 1 :: rest⟩ (f + 1) = some c := by
        rw [eval_step_continue rule445 _ _ f (carry_pos_step pre rest),
            show pre.length + 1 = (pre ++ [0]).length from by simp,
            show pre ++ 0 :: rest = (pre ++ [0]) ++ rest from by simp]
        exact he
      have hfb : fromBinary c.tape = fromBinary (pre ++ binarySucc (1 :: rest)) := by
        show fromBinary c.tape = fromBinary (pre ++ (0 :: binarySucc rest))
        rw [show pre ++ 0 :: binarySucc rest = (pre ++ [0]) ++ binarySucc rest from by simp]
        exact hf
      exact ⟨_, _, heval, hfb⟩

-- ============================================================================
-- Main theorem
-- ============================================================================

-- ============================================================================
-- The Universal Successor Simulation (Carry + Absorb + Walkback)
-- ============================================================================

/-- A walkback predicate: starting from state `startState` at position `pos`
    over an all-zero prefix `List.replicate n 0`, it eventually halts at
    position 0 with the same tape and some state. -/
def ValidWalkback (tm : TM) (startState : Nat) : Prop :=
  ∀ (n : Nat) (suf : List Nat) (pos : Nat), pos < n →
  (∀ d ∈ suf, d = 0 ∨ d = 1) →
  ∃ fuel endState, eval tm ⟨startState, pos, List.replicate n 0 ++ suf⟩ fuel =
    some ⟨endState, 0, List.replicate n 0 ++ suf⟩

/-- Main theorem: ANY Turing Machine matching the carry+absorb profile and having
    a valid walkback will compute the binary successor. -/
theorem sim_eval_universal (tm : TM) (as : Nat)
    (hcarry : tm.transition 1 1 = { nextState := 1, write := 0, dir := Dir.L })
    (habsorb : tm.transition 1 0 = { nextState := as, write := 1, dir := Dir.R })
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
        simp [step, readTape, List.getD, habsorb, writeTape, List.set]
      exact ⟨1, ⟨as, 0, [1]⟩, eval_step_halt _ _ _ 0 hs, by simp [fromBinary]⟩
    | succ m =>
      have hr : readTape (List.replicate (m + 1) 0) (m + 1) = 0 := rt_beyond _ _ (by simp)
      have hwt := wt_rep_extend (m + 1) 1
      have h_m0 : (m + 1 == 0) = false := by simp
      have ha : step tm ⟨1, m + 1, List.replicate (m + 1) 0⟩ =
          StepResult.continue ⟨as, m, List.replicate (m + 1) 0 ++ [1]⟩ := by
        unfold step; simp [hr, habsorb, h_m0, hwt]
      obtain ⟨fw, es, he⟩ := hwalkback (m + 1) [1] m (by omega) (by simp)
      exact ⟨fw + 1, ⟨es, 0, List.replicate (m + 1) 0 ++ [1]⟩,
        by rw [eval_step_continue _ _ _ _ ha]; exact he,
        rfl⟩
  | cons d rest ih =>
    have hbr : ∀ x ∈ rest, x = 0 ∨ x = 1 := fun x hx => hbs x (List.mem_cons_of_mem _ hx)
    rcases hbs d (List.mem_cons_self _ _) with rfl | rfl
    · -- d = 0: absorb → walk back
      simp only [binarySucc]
      cases n with
      | zero =>
        have hs : step tm ⟨1, 0, 0 :: rest⟩ = StepResult.halted ⟨as, 0, 1 :: rest⟩ := by
          simp [step, readTape, List.getD, habsorb, writeTape, List.set]
        exact ⟨1, ⟨as, 0, 1 :: rest⟩, eval_step_halt _ _ _ 0 hs, by simp [fromBinary]⟩
      | succ m =>
        have hr : readTape (List.replicate (m + 1) 0 ++ 0 :: rest) (m + 1) = 0 := rt_split (m + 1) 0 rest
        have h_m0 : (m + 1 == 0) = false := by simp
        have ha : step tm ⟨1, m + 1, List.replicate (m + 1) 0 ++ 0 :: rest⟩ =
            StepResult.continue ⟨as, m, List.replicate (m + 1) 0 ++ 1 :: rest⟩ := by
          unfold step; simp [hr, habsorb, h_m0, wt_split]
        obtain ⟨fw, es, he⟩ := hwalkback (m + 1) (1 :: rest) m (by omega) (by 
          intro x hx; simp at hx; cases hx with | inl h => exact Or.inr h | inr h => exact hbr x h)
        exact ⟨fw + 1, ⟨es, 0, List.replicate (m + 1) 0 ++ 1 :: rest⟩,
          by rw [eval_step_continue _ _ _ _ ha]; exact he, rfl⟩
    · -- d = 1: carry → recurse with prefix extended
      have hrd : readTape (List.replicate n 0 ++ 1 :: rest) n = 1 := rt_split n 1 rest
      have ha : step tm ⟨1, n, List.replicate n 0 ++ 1 :: rest⟩ =
          StepResult.continue ⟨1, n + 1, List.replicate (n + 1) 0 ++ rest⟩ := by
        simp [step, hrd, hcarry, wt_split, ← rep_snoc, List.append_assoc]
      obtain ⟨f, c, he, hf⟩ := ih (n + 1) hbr
      exact ⟨f + 1, c,
        by rw [eval_step_continue _ _ _ _ ha]; exact he,
        by rw [hf, show binarySucc (1 :: rest) = 0 :: binarySucc rest from rfl,
               ← rep_snoc n 0, List.append_assoc]; rfl⟩

/-- Rule 445 computes successor for all n ≥ 1. Formally proved by decomposing
    the TM execution into carry, absorb, and scanback phases via `sim_eval`. -/
theorem rule445_computesSucc : ComputesSucc rule445 := by
  intro n _hn
  obtain ⟨fuel, cfg, heval, hfb⟩ :=
    sim_eval [] (toBinary n) (fun _ h => absurd h (List.not_mem_nil _)) (toBinary_binary n)
  refine ⟨fuel, ?_⟩
  simp at heval hfb
  simp only [run, initConfig, heval, Option.map]
  simp only [outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

end OneSidedTM
