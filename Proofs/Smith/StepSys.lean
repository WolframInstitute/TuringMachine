/-
  Smith.StepSys

  A deterministic partial step system: a state type with a step function
  whose value is `none` exactly on the stuck states, and its iteration
  `StepSys.nSteps`. Every system of the chain (the Turing machine, the tag
  and cyclic tag systems, Systems 5 and 4, the lookahead machines, the
  infinite-tape machine) iterates through it.

  Contents: `StepSys`, `StepSys.nSteps`, `nSteps_zero`, `nSteps_succ_left`,
  `nSteps_one`, `nSteps_add`, `nSteps_succ`, `nSteps_some_of_le`,
  `step_some_of_nSteps`.
-/

namespace Smith

universe u v w

/-- A deterministic partial step system: a state type together with a step
    function whose value is `none` exactly on the stuck states. -/
structure StepSys (S : Type u) where
  /-- One step; `none` means the system is stuck. -/
  step : S → Option S

namespace StepSys

variable {S : Type u} {T : Type v} {U : Type w}

/-- `n` iterations of the step function; `none` as soon as one step is stuck. -/
def nSteps (M : StepSys S) (s : S) : Nat → Option S
  | 0 => some s
  | n + 1 =>
    match M.step s with
    | none => none
    | some s' => M.nSteps s' n

/-- Zero steps change nothing. -/
@[simp] theorem nSteps_zero (M : StepSys S) (s : S) : M.nSteps s 0 = some s := rfl

/-- One step peeled off the front. -/
theorem nSteps_succ_left (M : StepSys S) (s : S) (n : Nat) :
    M.nSteps s (n + 1) = (M.step s).bind (fun s' => M.nSteps s' n) := by
  cases h : M.step s <;> simp [nSteps, h]

/-- One step is the step function. -/
@[simp] theorem nSteps_one (M : StepSys S) (s : S) : M.nSteps s 1 = M.step s := by
  rw [nSteps_succ_left]
  cases M.step s <;> rfl

/-- Steps add. -/
theorem nSteps_add (M : StepSys S) (s : S) (n m : Nat) :
    M.nSteps s (n + m) = (M.nSteps s n).bind (fun s' => M.nSteps s' m) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add, nSteps_succ_left, nSteps_succ_left]
    cases h : M.step s with
    | none => simp
    | some s' => simp [ih]

/-- One step peeled off the back. -/
theorem nSteps_succ (M : StepSys S) (s : S) (n : Nat) :
    M.nSteps s (n + 1) = (M.nSteps s n).bind M.step := by
  rw [nSteps_add]
  simp

/-- A run of length `n` passes through a state at every earlier time. -/
theorem nSteps_some_of_le (M : StepSys S) (s s' : S) (n j : Nat)
    (hj : j ≤ n) (h : M.nSteps s n = some s') :
    ∃ sj, M.nSteps s j = some sj := by
  obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
  rw [nSteps_add] at h
  cases hh : M.nSteps s j with
  | none => rw [hh] at h; simp at h
  | some sj => exact ⟨sj, rfl⟩

/-- A run of positive length starts with a step. -/
theorem step_some_of_nSteps (M : StepSys S) (s s' : S) (k : Nat)
    (hk : 1 ≤ k) (h : M.nSteps s k = some s') :
    ∃ s1, M.step s = some s1 := by
  cases k with
  | zero => omega
  | succ j =>
    rw [nSteps_succ_left] at h
    cases hh : M.step s with
    | none => rw [hh] at h; simp at h
    | some s1 => exact ⟨s1, rfl⟩

end StepSys

end Smith
