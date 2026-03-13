/-
  OneSidedTM.ClassC

  Class C one-sided TMs: skip + right-absorb + clear-on-return.
  The (2,0) transition is dead (never fires during computation).
  All 8 rules 1512-1519 are Class C.
-/

import OneSidedTM.Basic
import OneSidedTM.PlusOne

namespace OneSidedTM
open TM

private theorem rs_ (pre : List Nat) (d : Nat) (suf : List Nat) :
    readTape (pre ++ d :: suf) pre.length = d := by
  induction pre with
  | nil => simp [readTape, List.getD]
  | cons _ rest ih => simp [readTape_cons_succ, ih]

private theorem rl_ (tape : List Nat) : readTape tape tape.length = 0 := by
  induction tape with
  | nil => simp [readTape, List.getD]
  | cons _ rest ih => simp [readTape_cons_succ, ih]

structure IsClassC (tm : TM) : Prop where
  skip : tm.transition 1 1 = { nextState := 1, write := 1, dir := Dir.L }
  absorb : tm.transition 1 0 = { nextState := 2, write := 1, dir := Dir.R }
  clear1 : tm.transition 2 1 = { nextState := 2, write := 0, dir := Dir.R }

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
  | zero => simp [writeTape, List.set, List.replicate]
  | succ k ih =>
    -- List.replicate (k+3) 1 ++ rest = 1 :: List.replicate (k+2) 1 ++ rest
    -- writeTape (1 :: ...) (k+2) 0 = 1 :: writeTape (...) (k+1) 0  via writeTape_cons_succ
    -- Then ih gives writeTape (List.replicate (k+2) 1 ++ rest) (k+1) 0 = List.replicate (k+1) 1 ++ 0 :: rest
    -- So 1 :: writeTape ... = 1 :: (List.replicate (k+1) 1 ++ 0 :: rest) = List.replicate (k+2) 1 ++ 0 :: rest
    -- Use unfold to keep types aligned
    unfold List.replicate
    rw [List.cons_append, writeTape_cons_succ]
    exact congrArg (1 :: ·) (ih rest)

theorem return_clear_ones (tm : TM) (hc : IsClassC tm) (k : Nat) (rest : List Nat) :
    eval tm ⟨2, k, List.replicate (k + 1) 1 ++ rest⟩ (k + 1) =
    some ⟨2, 0, List.replicate (k + 1) 0 ++ rest⟩ := by
  induction k generalizing rest with
  | zero =>
    have hs : step tm ⟨2, 0, 1 :: rest⟩ = StepResult.halted ⟨2, 0, 0 :: rest⟩ := by
      unfold step readTape; simp [List.getD, hc.clear1, writeTape]
    simp only [List.replicate]; exact eval_step_halt tm _ _ 0 hs
  | succ k ih =>
    have hr := readTape_replicate_succ k rest
    have hwt := writeTape_replicate_succ k rest
    have hs : step tm ⟨2, k + 1, List.replicate (k + 2) 1 ++ rest⟩ =
        StepResult.continue ⟨2, k, List.replicate (k + 1) 1 ++ 0 :: rest⟩ := by
      simp only [step, hr, hc.clear1, hwt]; simp
    rw [show (k + 1 + 1 : Nat) = (k + 1) + 1 from by omega,
        eval_step_continue tm _ _ (k + 1) hs]
    rw [replicate_append_one (k + 1) 0, List.append_assoc]
    simp only [List.singleton_append]
    exact ih (0 :: rest)

private theorem ones_eq_rep (l : List Nat) (h : ∀ (d : Nat), d ∈ l → d = 1) :
    l = List.replicate l.length 1 := by
  induction l with
  | nil => rfl
  | cons d rest ih =>
    have hd := h d (List.mem_cons_self _ _)
    subst hd
    exact congrArg (1 :: ·) (ih (fun (x : Nat) (hx : x ∈ rest) => h x (List.mem_cons_of_mem _ hx)))

private theorem binarySucc_ones_fb (k : Nat) :
    fromBinary (List.replicate k 0 ++ [1]) = fromBinary (binarySucc (List.replicate k 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, binarySucc, fromBinary, List.append_cons]; simp [ih]

private theorem binarySucc_ones_zero_fb (k : Nat) (rest : List Nat) :
    fromBinary (List.replicate k 0 ++ 1 :: rest) =
    fromBinary (binarySucc (List.replicate k 1 ++ 0 :: rest)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, binarySucc, fromBinary]; simp [ih]

theorem sim_eval_C (tm : TM) (hc : IsClassC tm) (pre suf : List Nat)
    (hbp : ∀ (d : Nat), d ∈ pre → d = 1)
    (hbs : ∀ (d : Nat), d ∈ suf → d = 0 ∨ d = 1) :
    ∃ fuel cfg, eval tm ⟨1, pre.length, pre ++ suf⟩ fuel = some cfg ∧
    fromBinary cfg.tape = fromBinary (binarySucc (pre ++ suf)) := by
  induction suf generalizing pre with
  | nil =>
    by_cases hp : pre.length = 0
    · have hpnil := List.length_eq_zero.mp hp; subst hpnil
      simp only [List.append_nil, binarySucc]
      have hab : step tm ⟨1, 0, []⟩ = StepResult.halted ⟨2, 0, [1]⟩ := by
        unfold step readTape; simp [List.getD, hc.absorb, writeTape]
      exact ⟨1, _, eval_step_halt tm _ _ 0 hab, rfl⟩
    · simp only [List.append_nil]
      have hrep := ones_eq_rep pre hbp
      have hplen : (pre.length - 1) + 1 = pre.length := by omega
      have hab : step tm ⟨1, pre.length, pre⟩ =
          StepResult.continue ⟨2, pre.length - 1, pre ++ [1]⟩ := by
        simp only [step, rl_ pre, hc.absorb, Dir.R]
        have : (pre.length == 0) = false := by
          cases pre with | nil => simp at hp | cons _ _ => simp
        rw [this]; simp [writeTape]
      have heval : eval tm ⟨1, pre.length, pre⟩ (pre.length + 1) =
          some ⟨2, 0, List.replicate pre.length 0 ++ [1]⟩ := by
        rw [eval_step_continue tm _ _ _ hab, hrep]
        simp only [List.length_replicate]; rw [← hplen]
        exact return_clear_ones tm hc (pre.length - 1) [1]
      exact ⟨_, _, heval, by
        rw [hrep]; simp only [List.length_replicate]
        exact binarySucc_ones_fb pre.length⟩

  | cons d rest ih =>
    have hbr : ∀ (x : Nat), x ∈ rest → x = 0 ∨ x = 1 :=
      fun x hx => hbs x (List.mem_cons_of_mem _ hx)
    rcases hbs d (List.mem_cons_self _ _) with rfl | rfl
    · by_cases hp : pre.length = 0
      · have hpnil := List.length_eq_zero.mp hp; subst hpnil; simp
        have hab : step tm ⟨1, 0, 0 :: rest⟩ = StepResult.halted ⟨2, 0, 1 :: rest⟩ := by
          unfold step readTape; simp [List.getD, hc.absorb, writeTape]
        exact ⟨1, _, eval_step_halt tm _ _ 0 hab, by simp [binarySucc]⟩
      · have hrep := ones_eq_rep pre hbp
        have hplen : (pre.length - 1) + 1 = pre.length := by omega
        have hab : step tm ⟨1, pre.length, pre ++ 0 :: rest⟩ =
            StepResult.continue ⟨2, pre.length - 1, pre ++ 1 :: rest⟩ := by
          simp only [step, rs_ pre 0 rest, hc.absorb, Dir.R]
          have : (pre.length == 0) = false := by
            cases pre with | nil => simp at hp | cons _ _ => simp
          rw [this]; simp [writeTape_append pre 0 rest 1]
        have heval : eval tm ⟨1, pre.length, pre ++ 0 :: rest⟩ (pre.length + 1) =
            some ⟨2, 0, List.replicate pre.length 0 ++ 1 :: rest⟩ := by
          rw [eval_step_continue tm _ _ _ hab, hrep]
          simp only [List.length_replicate]
          rw [← hplen]
          exact return_clear_ones tm hc (pre.length - 1) (1 :: rest)
        exact ⟨_, _, heval, by
          rw [hrep]; simp only [List.length_replicate]
          exact binarySucc_ones_zero_fb pre.length rest⟩

    · have hbp' : ∀ (x : Nat), x ∈ pre ++ [1] → x = 1 := by
        intro x hx; simp at hx; rcases hx with h | h; exact hbp x h; exact h
      obtain ⟨f, c, he, hf⟩ := ih (pre ++ [1]) hbp' hbr
      have hskip : step tm ⟨1, pre.length, pre ++ 1 :: rest⟩ =
          StepResult.continue ⟨1, pre.length + 1, pre ++ 1 :: rest⟩ := by
        simp only [step, rs_ pre 1 rest, hc.skip]
        have hwt := writeTape_val_eq_id (pre ++ 1 :: rest) pre.length 1
          (by simp) (rs_ pre 1 rest)
        simp [Dir.L, hwt]
      exact ⟨_, _, by
        rw [eval_step_continue tm _ _ f hskip,
            show pre.length + 1 = (pre ++ [1]).length from by simp,
            show pre ++ 1 :: rest = (pre ++ [1]) ++ rest from by simp]; exact he,
        by rw [show pre ++ 1 :: rest = (pre ++ [1]) ++ rest from by simp]; exact hf⟩

theorem classC_computesSucc (tm : TM) (hc : IsClassC tm) : ComputesSucc tm := by
  intro n _hn
  obtain ⟨fuel, cfg, heval, hfb⟩ :=
    sim_eval_C tm hc [] (toBinary n) (fun _ h => absurd h (List.not_mem_nil _)) (toBinary_binary n)
  refine ⟨fuel, ?_⟩; simp at heval hfb
  simp only [run, initConfig, heval, Option.map, outputValue, fromBinary_trim, hfb]
  rw [fromBinary_binarySucc _ (toBinary_binary n), fromBinary_toBinary]

end OneSidedTM
