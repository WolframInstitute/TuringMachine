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
-- Tape identity: writeTape preserves tape when writing same value
-- ============================================================================

theorem writeTape_read_id (tape : List Nat) (pos : Nat) (h : pos < tape.length) :
    writeTape tape pos (readTape tape pos) = tape := by
  induction tape generalizing pos with
  | nil => simp at h
  | cons d rest ih =>
    cases pos with
    | zero => simp [writeTape, readTape, List.getD, List.set]
    | succ p =>
      have hp : p < rest.length := by simp at h; omega
      simp only [readTape_cons_succ, writeTape_cons_succ]; congr 1; exact ih p hp

theorem writeTape_val_eq_id (tape : List Nat) (pos v : Nat)
    (hlen : pos < tape.length) (hval : readTape tape pos = v) :
    writeTape tape pos v = tape := by
  rw [← hval]; exact writeTape_read_id tape pos hlen

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
-- ============================================================================
-- eval fuel monotonicity
-- ============================================================================

theorem eval_mono (tm : TM) (cfg r : Config) :
    ∀ fuel : Nat, eval tm cfg fuel = some r → ∀ fuel', fuel ≤ fuel' →
    eval tm cfg fuel' = some r := by
  intro fuel; induction fuel generalizing cfg with
  | zero => intro h; simp [eval] at h
  | succ f ih =>
    intro h fuel' hle; cases fuel' with | zero => omega | succ f' =>
    unfold eval at h ⊢
    match hs : step tm cfg with
    | StepResult.halted cfg' => simp [hs] at h ⊢; exact h
    | StepResult.continue cfg' => simp [hs] at h ⊢; exact ih cfg' h f' (by omega)

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
-- Step count
-- ============================================================================

def leadingOnes : List Nat → Nat
  | 1 :: rest => 1 + leadingOnes rest
  | _ => 0

def rule445Fuel (n : Nat) : Nat :=
  2 * leadingOnes (toBinary n) + 3

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- Rule 445 computes successor for all n ≥ 1.

    All supporting lemmas are fully proved:
    1. toBinary_succ: toBinary (n+1) = binarySucc (toBinary n) ✓
    2. fromBinary_binarySucc: fromBinary (binarySucc t) = fromBinary t + 1 ✓
    3. fromBinary_toBinary: fromBinary (toBinary n) = n ✓
    4. fromBinary_trim: trimTrailingZeros preserves fromBinary ✓
    5. TM phase lemmas: carry, absorb, scanback_eval, halt_step_id ✓
    6. eval_mono: fuel monotonicity ✓
    7. readTape/writeTape lemmas ✓

    The remaining sorry is purely the assembly of these lemmas into a
    complete eval chain (composing carry→absorb→scanback→halt by induction
    on the tape structure with a generalized prefix).

    Machine-checked evidence: rule445_succ_bulk verifies all n ∈ [1..65535]. -/
theorem rule445_computesSucc : ComputesSucc rule445 := by
  intro n hn
  exact ⟨rule445Fuel n + 5, sorry⟩

end OneSidedTM
