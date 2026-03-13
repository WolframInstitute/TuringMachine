/-
  OneSidedTM.ClassR — Reverse-direction +1 algorithms (Groups 19-22, 12 rules)

  Sub-class RC (Reverse Carry, Groups 19-20, 8 rules):
    State 1→α flips 1→0 left. α reads 0 → β writes 1 right. β walks right to halt.

  Sub-class RS (Reverse Scan, Groups 21-22, 4 rules):
    State 1 scans left past 1s. Overshoots to α. α→β turns around.
    β sets MSB then flips 1→0 right until halt.
-/
import OneSidedTM.Basic
import OneSidedTM.PlusOne

namespace OneSidedTM
open TM

-- ============================================================
-- Tape helper
-- ============================================================

private theorem readTape_zeros (pre : List Nat) (suf : List Nat)
    (hp : ∀ d ∈ pre, d = 0) (i : Nat) (hi : i < pre.length) :
    readTape (pre ++ suf) i = 0 := by
  induction pre generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero => simp [readTape_cons_zero]; exact hp a (List.mem_cons_self _ _)
    | succ j =>
      simp [readTape_cons_succ]
      exact ih (fun d hd => hp d (List.mem_cons_of_mem _ hd)) j (by simp at hi; omega)

-- ============================================================
-- Sub-class RC: Reverse Carry (Groups 19-20)
-- ============================================================

structure IsClassRC (tm : TM) (α β : Nat) : Prop where
  start   : tm.transition 1 1 = { nextState := α, write := 0, dir := Dir.L }
  carry   : tm.transition α 1 = { nextState := α, write := 0, dir := Dir.L }
  absorb  : tm.transition α 0 = { nextState := β, write := 1, dir := Dir.R }
  walk    : tm.transition β 0 = { nextState := β, write := 0, dir := Dir.R }

-- ============================================================
-- Step lemmas
-- ============================================================

private theorem rc_carry_pos (tm : TM) (α β : Nat) (hc : IsClassRC tm α β)
    (pre suf : List Nat) :
    step tm ⟨α, pre.length, pre ++ 1 :: suf⟩ =
    StepResult.continue ⟨α, pre.length + 1, pre ++ 0 :: suf⟩ := by
  unfold step; simp only [readTape_append, readTape_cons_zero, hc.carry,
             writeTape_append, writeTape_cons_zero]

private theorem rc_absorb_pos (tm : TM) (α β : Nat) (hc : IsClassRC tm α β)
    (pre suf : List Nat) (hp : pre.length > 0) :
    step tm ⟨α, pre.length, pre ++ 0 :: suf⟩ =
    StepResult.continue ⟨β, pre.length - 1, pre ++ 1 :: suf⟩ := by
  unfold step
  simp only [readTape_append, readTape_cons_zero, hc.absorb,
             writeTape_append, writeTape_cons_zero, Dir.R]
  have : (pre.length == 0) = false := by
    cases pre with | nil => simp at hp | cons _ _ => rfl
  rw [this]; rfl

-- ============================================================
-- Walk phase: β walks from position p to 0 through zeros
-- ============================================================

private theorem rc_walk_chain (tm : TM) (α β : Nat) (hc : IsClassRC tm α β)
    (tape : List Nat) (p : Nat)
    (h0 : ∀ i, 0 < i → i ≤ p → readTape tape i = 0)
    (hhalt : readTape tape 0 = 0)
    (hlen : ∀ i, i ≤ p → i < tape.length) :
    eval tm ⟨β, p, tape⟩ (p + 1) = some ⟨β, 0, tape⟩ := by
  induction p with
  | zero =>
    rw [show (0 + 1 : Nat) = 0 + 1 from rfl]
    exact eval_step_halt tm _ _ 0
      (by unfold step; simp only [hhalt, hc.walk, writeTape_cons_zero]
          simp [writeTape_val_eq_id tape 0 0 (hlen 0 (by omega)) hhalt])
  | succ m ih =>
    rw [show (m + 1 + 1 : Nat) = (m + 1) + 1 from by omega]
    have hr : readTape tape (m + 1) = 0 := h0 (m + 1) (by omega) (by omega)
    have hwrite : writeTape tape (m + 1) 0 = tape :=
      writeTape_val_eq_id tape (m + 1) 0 (hlen (m + 1) (by omega)) hr
    have hstep : step tm ⟨β, m + 1, tape⟩ = StepResult.continue ⟨β, m, tape⟩ := by
      unfold step; simp only [hr, hc.walk, Dir.R, hwrite]; rfl
    rw [eval_step_continue tm _ _ (m + 1) hstep]
    exact ih (fun i hi1 hi2 => h0 i hi1 (by omega)) (fun i hi => hlen i (by omega))

-- ============================================================
-- Core simulation: carry + absorb + walk as single eval
--   Fuel: 2*k + |pre| + 1  (k carry + 1 absorb + (k+|pre|) walk)
-- ============================================================

private theorem sim_eval_rc (tm : TM) (α β : Nat) (hc : IsClassRC tm α β)
    (k : Nat) (pre suf : List Nat) (hp : ∀ d ∈ pre, d = 0) (hplen : pre.length > 0) :
    eval tm ⟨α, pre.length, pre ++ List.replicate k 1 ++ 0 :: suf⟩
      (2 * k + pre.length + 1) =
    some ⟨β, 0, pre ++ List.replicate k 0 ++ 1 :: suf⟩ := by
  induction k generalizing pre with
  | zero =>
    simp only [List.replicate, List.nil_append, List.append_nil]
    rw [show 2 * 0 + pre.length + 1 = pre.length + 1 from by omega]
    rw [eval_step_continue tm _ _ pre.length (rc_absorb_pos tm α β hc pre suf hplen)]
    rw [show pre.length = (pre.length - 1) + 1 from by omega]
    exact rc_walk_chain tm α β hc (pre ++ 1 :: suf) (pre.length - 1)
      (fun i hi1 hi2 => readTape_zeros pre (1 :: suf) hp i (by omega))
      (readTape_zeros pre (1 :: suf) hp 0 hplen)
      (fun i hi => by simp; omega)
  | succ m ih =>
    rw [show 2 * (m + 1) + pre.length + 1 = (2 * m + (pre.length + 1) + 1) + 1 from by omega]
    simp only [List.replicate_succ, List.cons_append, List.append_assoc]
    rw [eval_step_continue tm _ _ (2 * m + (pre.length + 1) + 1)
        (rc_carry_pos tm α β hc pre (List.replicate m 1 ++ 0 :: suf))]
    have hih := ih (pre ++ [0])
      (by intro d hd; simp at hd; cases hd with
          | inl h => exact hp d h | inr h => exact h)
      (by simp)
    simp only [List.length_append, List.length_singleton,
               List.append_assoc, List.singleton_append] at hih
    exact hih

-- ============================================================
-- Main theorem: reverse_carry_ones
-- ============================================================

/-- ClassRC computes +1 on all-ones blocks:
    Input:  ⟨1, 0, [1,...,1, 0, ...suf]⟩  (n ones followed by 0)
    Output: ⟨β, 0, [0,...,0, 1, ...suf]⟩  (n zeros followed by 1)
    Transforms binary 2^n - 1 → 2^n.
    Uses 2n + 1 steps. -/
theorem reverse_carry_ones (tm : TM) (α β : Nat) (hc : IsClassRC tm α β)
    (n : Nat) (suf : List Nat) (hn : n > 0) :
    ∃ fuel, eval tm ⟨1, 0, List.replicate n 1 ++ 0 :: suf⟩ fuel =
      some ⟨β, 0, List.replicate n 0 ++ 1 :: suf⟩ := by
  refine ⟨2 * n + 1, ?_⟩
  have htape : List.replicate n 1 ++ 0 :: suf = 1 :: (List.replicate (n - 1) 1 ++ 0 :: suf) := by
    cases n with | zero => omega | succ m => simp [List.replicate_succ]
  rw [htape]
  rw [show 2 * n + 1 = (2 * (n - 1) + 1 + 1) + 1 from by omega]
  have hstart : step tm ⟨1, 0, 1 :: (List.replicate (n - 1) 1 ++ 0 :: suf)⟩ =
      StepResult.continue ⟨α, 1, 0 :: (List.replicate (n - 1) 1 ++ 0 :: suf)⟩ := by
    unfold step; simp only [readTape_cons_zero, hc.start, writeTape_cons_zero]
  rw [eval_step_continue tm _ _ (2 * (n - 1) + 1 + 1) hstart]
  have hih := sim_eval_rc tm α β hc (n - 1) [0] suf (by simp) (by simp)
  simp only [List.length_singleton, List.singleton_append, List.append_assoc] at hih
  show eval tm ⟨α, 1, 0 :: (List.replicate (n - 1) 1 ++ 0 :: suf)⟩ (2 * (n - 1) + 1 + 1) =
    some ⟨β, 0, List.replicate n 0 ++ 1 :: suf⟩
  rw [show List.replicate n 0 ++ 1 :: suf = [0] ++ List.replicate (n - 1) 0 ++ 1 :: suf
      from by cases n with | zero => omega | succ m => simp [List.replicate_succ]]
  exact hih

-- ============================================================
-- Sub-class RS: Reverse Scan (Groups 21-22)
-- ============================================================

structure IsClassRS (tm : TM) (α β : Nat) : Prop where
  scan    : tm.transition 1 1 = { nextState := 1, write := 1, dir := Dir.L }
  over    : tm.transition 1 0 = { nextState := α, write := 0, dir := Dir.L }
  turn    : tm.transition α 0 = { nextState := β, write := 0, dir := Dir.R }
  turn1   : tm.transition α 1 = { nextState := β, write := 1, dir := Dir.R }
  set_msb : tm.transition β 0 = { nextState := β, write := 1, dir := Dir.R }
  clear   : tm.transition β 1 = { nextState := β, write := 0, dir := Dir.R }

-- ============================================================
-- Helpers for reverse_scan_ones
-- ============================================================

-- readTape in ones region
private theorem rt_ones (n : Nat) (rest : List Nat) (i : Nat) (h : i < n) :
    readTape (List.replicate n 1 ++ rest) i = 1 := by
  induction n generalizing i with
  | zero => omega
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (1 :: List.replicate m 1) ++ rest = 1 :: (List.replicate m 1 ++ rest) from by simp]
    cases i with
    | zero => simp [readTape_cons_zero]
    | succ j => simp only [readTape_cons_succ]; exact ih j (by omega)

-- readTape at boundary
private theorem rt_at_sep' (n : Nat) (d : Nat) (rest : List Nat) :
    readTape (List.replicate n 1 ++ d :: rest) n = d := by
  induction n with
  | zero => simp [readTape, List.getD]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (1 :: List.replicate m 1) ++ d :: rest =
      1 :: (List.replicate m 1 ++ d :: rest) from by simp, readTape_cons_succ]; exact ih

-- writeTape at boundary
private theorem wt_at_sep' (n : Nat) (d : Nat) (rest : List Nat) (v : Nat) :
    writeTape (List.replicate n 1 ++ d :: rest) n v =
    List.replicate n 1 ++ v :: rest := by
  induction n with
  | zero => simp [writeTape, List.set]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (1 :: List.replicate m 1) ++ d :: rest =
      1 :: (List.replicate m 1 ++ d :: rest) from by simp, writeTape_cons_succ]
    rw [ih]; simp [List.replicate_succ]

-- readTape past boundary
private theorem rt_past_sep (n : Nat) (d : Nat) (rest : List Nat) :
    readTape (List.replicate n 1 ++ d :: rest) (n + 1) = readTape rest 0 := by
  induction n with
  | zero => simp [readTape_cons_succ]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (1 :: List.replicate m 1) ++ d :: rest =
      1 :: (List.replicate m 1 ++ d :: rest) from by simp, readTape_cons_succ]; exact ih

-- writeTape past boundary
private theorem wt_past_sep (n : Nat) (d : Nat) (rest : List Nat) (v : Nat) :
    writeTape (List.replicate n 1 ++ d :: rest) (n + 1) v =
    List.replicate n 1 ++ d :: writeTape rest 0 v := by
  induction n with
  | zero => simp [writeTape_cons_succ, writeTape_cons_zero]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (1 :: List.replicate m 1) ++ d :: rest =
      1 :: (List.replicate m 1 ++ d :: rest) from by simp, writeTape_cons_succ]
    rw [ih]; simp [List.replicate_succ]

private theorem rep_0_cons' (n : Nat) (rest : List Nat) :
    List.replicate n 0 ++ 0 :: rest = List.replicate (n + 1) 0 ++ rest := by
  induction n with
  | zero => simp
  | succ m ih => simp [List.replicate_succ]; exact ih

-- writeTape at k in rep (k+1) 1 ++ rest, writing 0
private theorem wt_clear_k' (k : Nat) (rest : List Nat) :
    writeTape (List.replicate (k + 1) 1 ++ rest) k 0 =
    List.replicate k 1 ++ (0 :: rest) := by
  induction k with
  | zero => simp [writeTape_cons_zero]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (1 :: List.replicate (m + 1) 1) ++ rest =
      1 :: (List.replicate (m + 1) 1 ++ rest) from by simp, writeTape_cons_succ]
    rw [ih]; simp [List.replicate_succ]

private theorem eval_step_halted (tm : TM) (cfg cfg' : Config)
    (h : step tm cfg = StepResult.halted cfg') :
    eval tm cfg 1 = some cfg' := by simp [eval, h]

-- ============================================================
-- Phase 1: Scan — state 1 scans left through k ones
-- ============================================================

private theorem rs_scan_ex (tm : TM) (α β : Nat) (hc : IsClassRS tm α β)
    (tape : List Nat) (k : Nat) (i : Nat)
    (h_read : ∀ j, i ≤ j → j < i + k → readTape tape j = 1)
    (h_len : ∀ j, i ≤ j → j < i + k → j < tape.length)
    {cfg : Config} (h_next : ∃ fuel, eval tm ⟨1, i + k, tape⟩ fuel = some cfg) :
    ∃ fuel, eval tm ⟨1, i, tape⟩ fuel = some cfg := by
  induction k generalizing i with
  | zero => simpa using h_next
  | succ m ih =>
    have hr := h_read i (Nat.le_refl _) (by omega)
    have hl := h_len i (Nat.le_refl _) (by omega)
    have hs : step tm ⟨1, i, tape⟩ = StepResult.continue ⟨1, i + 1, tape⟩ := by
      simp only [step, hr, hc.scan, writeTape_val_eq_id tape i 1 hl hr]
    have h_next' : ∃ fuel, eval tm ⟨1, (i + 1) + m, tape⟩ fuel = some cfg := by
      rw [show (i + 1) + m = i + (m + 1) from by omega]; exact h_next
    obtain ⟨fm, hm⟩ := ih (i + 1)
      (fun j hj hj' => h_read j (by omega) (by omega))
      (fun j hj hj' => h_len j (by omega) (by omega))
      h_next'
    exact ⟨fm + 1, by rw [eval_step_continue _ _ _ _ hs]; exact hm⟩

-- ============================================================
-- Phase 5: Clear — β clears k+1 ones, halting at pos 0
-- ============================================================

private theorem rs_clear (tm : TM) (α β : Nat) (hc : IsClassRS tm α β)
    (k : Nat) (rest : List Nat) :
    ∃ fuel, eval tm ⟨β, k, List.replicate (k + 1) 1 ++ rest⟩ fuel =
      some ⟨β, 0, List.replicate (k + 1) 0 ++ rest⟩ := by
  induction k generalizing rest with
  | zero =>
    have hs : step tm ⟨β, 0, 1 :: rest⟩ = StepResult.halted ⟨β, 0, 0 :: rest⟩ := by
      unfold step; simp [readTape_cons_zero, hc.clear, writeTape_cons_zero]
    exact ⟨1, eval_step_halted tm _ _ hs⟩
  | succ m ih =>
    have hs : step tm ⟨β, m + 1, List.replicate (m + 2) 1 ++ rest⟩ =
        StepResult.continue ⟨β, m, List.replicate (m + 1) 1 ++ (0 :: rest)⟩ := by
      simp only [step, rt_ones (m + 2) rest (m + 1) (by omega), hc.clear,
                  wt_clear_k' (m + 1) rest]
      have h1 : (m + 1 == 0) = false := by cases m <;> rfl
      simp [h1, show m + 1 - 1 = m from by omega]
    obtain ⟨fw, hew⟩ := ih (0 :: rest)
    refine ⟨fw + 1, ?_⟩
    rw [eval_step_continue _ _ _ _ hs, ← rep_0_cons' (m + 1) rest]
    exact hew

-- ============================================================
-- Main theorem: reverse scan ones
-- ============================================================

private abbrev rsTape (p : Nat) (suf : List Nat) : List Nat :=
  List.replicate (p + 1) 1 ++ 0 :: suf

/-- Reverse scan: state 1 scans n ones backward, then the fill-turn-clear
    cycle produces the reversed tape. Requires suf to be non-empty with
    binary digits so the turn step at position n+1 reads within bounds. -/
theorem reverse_scan_ones (tm : TM) (α β : Nat) (hc : IsClassRS tm α β)
    (n : Nat) (suf : List Nat) (hn : n > 0)
    (hsuf : suf.length > 0) (hbs : ∀ d ∈ suf, d = 0 ∨ d = 1) :
    ∃ fuel, eval tm ⟨1, 0, List.replicate n 1 ++ 0 :: suf⟩ fuel =
      some ⟨β, 0, List.replicate n 0 ++ 1 :: suf⟩ := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  -- Phase 5: Clear from (β, p) on rep (p+1) 1 ++ 1::suf
  obtain ⟨f_c, h_c⟩ := rs_clear tm α β hc p (1 :: suf)
  -- Phase 4: Set MSB at pos p+1 (reads 0, writes 1)
  have hs_msb : step tm ⟨β, p + 1, rsTape p suf⟩ =
      StepResult.continue ⟨β, p, List.replicate (p + 1) 1 ++ 1 :: suf⟩ := by
    unfold step
    simp only [rsTape, rt_at_sep' (p + 1) 0 suf, hc.set_msb,
               wt_at_sep' (p + 1) 0 suf 1]
    have : (p + 1 == 0) = false := by cases p <;> rfl
    rw [this]; simp [show p + 1 - 1 = p from by omega]
  have h4 : ∃ fuel, eval tm ⟨β, p + 1, rsTape p suf⟩ fuel =
      some ⟨β, 0, List.replicate (p + 1) 0 ++ 1 :: suf⟩ :=
    ⟨f_c + 1, by rw [eval_step_continue _ _ _ _ hs_msb]; exact h_c⟩
  -- Phase 3: Turn at pos p+2 (reads suf[0], writes suf[0] back)
  have hr_turn : readTape (rsTape p suf) (p + 2) = readTape suf 0 :=
    rt_past_sep (p + 1) 0 suf
  have hsuf0 : readTape suf 0 = 0 ∨ readTape suf 0 = 1 := by
    cases suf with
    | nil => simp at hsuf
    | cons d rest => simp [readTape_cons_zero]; exact hbs d (List.mem_cons_self _ _)
  have hwt_turn : writeTape (rsTape p suf) (p + 2) (readTape suf 0) = rsTape p suf := by
    simp only [rsTape, wt_past_sep (p + 1) 0 suf]
    cases suf with
    | nil => simp at hsuf
    | cons d rest => simp [readTape_cons_zero, writeTape_cons_zero]
  have hs_turn : step tm ⟨α, p + 2, rsTape p suf⟩ =
      StepResult.continue ⟨β, p + 1, rsTape p suf⟩ := by
    unfold step; rw [hr_turn]
    rcases hsuf0 with h | h
    · simp only [h, hc.turn]
      rw [show writeTape (rsTape p suf) (p + 2) 0 = rsTape p suf from
        by rw [← h, hwt_turn]]
      simp [show p + 2 - 1 = p + 1 from by omega,
            show (p + 2 == 0) = false from by cases p <;> rfl]
    · simp only [h, hc.turn1]
      rw [show writeTape (rsTape p suf) (p + 2) 1 = rsTape p suf from
        by rw [← h, hwt_turn]]
      simp [show p + 2 - 1 = p + 1 from by omega,
            show (p + 2 == 0) = false from by cases p <;> rfl]
  obtain ⟨f4, h4'⟩ := h4
  have h3 : ∃ fuel, eval tm ⟨α, p + 2, rsTape p suf⟩ fuel =
      some ⟨β, 0, List.replicate (p + 1) 0 ++ 1 :: suf⟩ :=
    ⟨f4 + 1, by rw [eval_step_continue _ _ _ _ hs_turn]; exact h4'⟩
  -- Phase 2: Over at pos p+1 (reads 0, writes 0, nop)
  have hs_over : step tm ⟨1, p + 1, rsTape p suf⟩ =
      StepResult.continue ⟨α, p + 2, rsTape p suf⟩ := by
    simp only [step, rsTape, rt_at_sep' (p + 1) 0 suf, hc.over]
    simp [wt_at_sep' (p + 1) 0 suf 0]
  obtain ⟨f3, h3'⟩ := h3
  have h2 : ∃ fuel, eval tm ⟨1, p + 1, rsTape p suf⟩ fuel =
      some ⟨β, 0, List.replicate (p + 1) 0 ++ 1 :: suf⟩ :=
    ⟨f3 + 1, by rw [eval_step_continue _ _ _ _ hs_over]; exact h3'⟩
  -- Phase 1: Scan p+1 ones from pos 0
  have h2' : ∃ fuel, eval tm ⟨1, 0 + (p + 1), rsTape p suf⟩ fuel =
      some ⟨β, 0, List.replicate (p + 1) 0 ++ 1 :: suf⟩ := by
    simpa using h2
  exact rs_scan_ex tm α β hc (rsTape p suf) (p + 1) 0
    (fun j _ hj => by simp only [rsTape]; exact rt_ones (p + 1) (0 :: suf) j (by omega))
    (fun j _ hj => by simp only [rsTape]; simp; omega)
    h2'

end OneSidedTM
