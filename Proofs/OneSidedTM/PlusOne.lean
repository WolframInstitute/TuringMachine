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
-- Machine-checked proofs for specific inputs (19 theorems)
-- ============================================================================

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
-- eval composition lemma
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
-- TM phase simulation lemmas
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

@[simp] theorem readTape_cons_zero (d : Nat) (rest : List Nat) :
    readTape (d :: rest) 0 = d := by simp [readTape, List.getD]

@[simp] theorem readTape_cons_succ (d : Nat) (rest : List Nat) (n : Nat) :
    readTape (d :: rest) (n + 1) = readTape rest n := by simp [readTape, List.getD]

@[simp] theorem readTape_nil (pos : Nat) : readTape [] pos = 0 := by
  simp [readTape, List.getD]

@[simp] theorem writeTape_cons_zero (d : Nat) (rest : List Nat) (v : Nat) :
    writeTape (d :: rest) 0 v = v :: rest := by simp [writeTape, List.set]

@[simp] theorem writeTape_cons_succ (d : Nat) (rest : List Nat) (n : Nat) (v : Nat) :
    writeTape (d :: rest) (n + 1) v = d :: writeTape rest n v := by
  simp [writeTape]; split <;> simp [List.set]

-- ============================================================================
-- Step count
-- ============================================================================

def leadingOnes : List Nat → Nat
  | 1 :: rest => 1 + leadingOnes rest
  | _ => 0

def rule445Fuel (n : Nat) : Nat :=
  2 * leadingOnes (toBinary n) + 3

#eval (List.range 20).map fun i =>
  let n := i + 1
  (n, rule445Fuel n, checkRun rule445 n (rule445Fuel n) (n + 1))

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- Rule 445 computes successor for all n ≥ 1.

    Proved components:
    1. toBinary_succ: toBinary (n+1) = binarySucc (toBinary n) ✓
    2. fromBinary_binarySucc: fromBinary (binarySucc t) = fromBinary t + 1 ✓
    3. fromBinary_toBinary: fromBinary (toBinary n) = n ✓
    4. TM phase lemmas: carry_step, absorb_step, scanback, halt ✓

    Remaining: assembling Phase 4 into a simulation that shows
    eval rule445 (initConfig n) fuel produces a tape whose
    trimmed output equals n+1. -/
theorem rule445_computesSucc : ComputesSucc rule445 := by
  intro n hn
  exact ⟨rule445Fuel n + 5, sorry⟩

end OneSidedTM
