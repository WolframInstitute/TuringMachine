/-
  BiTM.System4

  Smith's "System 4" simulator (PDF `TM23Proof.pdf` p. 34, `system4.pl`):
  a star/set-tape automaton with 3-state head (A/B/C) emulating
  System 5 (`cy2s4.pl` PDF p. 32 encodes System 5 -> System 4).

  Contents:
    * `System4State`, `System4Elem`, `System4Config`
    * `decrementSet`: helper for rule 3
    * `System4.step`: 5-rule dispatch on (state, elems[active])
    * `System4.nSteps`: multi-step runner
    * `nSteps_zero/one/add/succ`: structural lemmas
    * Sanity-check examples against PDF traces
-/

import BiTM.XorMerge
import BiTM.HaltInduction
import TagSystem.HaltsEmpty

namespace BiTM

open TM
open TagSystem

/-- System 4's state alphabet: A, B, or C. -/
inductive System4State : Type
  | A : System4State
  | B : System4State
  | C : System4State
  deriving DecidableEq, Repr

/-- System 4's tape elements: either a star `_` or a finite multiset of integers
    (represented as `List Int` with the same parity-mod-2 semantics as System 5). -/
inductive System4Elem : Type
  | star : System4Elem
  | set : List Int → System4Elem
  deriving DecidableEq, Repr

/-- A System 4 configuration: tape elements + active index + current state. -/
structure System4Config where
  elems : List System4Elem
  active : Nat
  state : System4State
  deriving DecidableEq, Repr

/-- Decrement every integer in a System 4 set, returning the new set plus
    a boolean indicating whether `0` was present (and so its decrement
    would change state).  Per `system4.pl`: `0` keys toggle state but
    are NOT included in the decremented result. -/
def decrementSet (s : List Int) : List Int × Bool :=
  if 0 ∈ s then ((s.erase 0).map (· - 1), true)
  else (s.map (· - 1), false)

/-- Sanity check `decrementSet` matches the perl semantics: `[0, 6, 8]` ->
    `([5, 7], true)` (the 0 is removed and triggers state toggle, others
    decrement to 5 and 7). -/
example : decrementSet [0, 6, 8] = ([5, 7], true) := by decide

/-- Sanity check: `[3, 4]` (no `0`) -> `([2, 3], false)`. -/
example : decrementSet [3, 4] = ([2, 3], false) := by decide

/-- The boolean component of `decrementSet s` is `true` exactly when `0 in s`.
    Direct from the definition. -/
theorem decrementSet_snd_iff_mem_zero (s : List Int) :
    (decrementSet s).snd = true ↔ 0 ∈ s := by
  unfold decrementSet
  by_cases h : 0 ∈ s
  · simp [h]
  · simp [h]

/-- If `0 not in s`, the decremented set has the same length as `s`; if `0 in
    s`, the length is `s.length - 1` (the `0` is removed before mapping). -/
theorem decrementSet_fst_length (s : List Int) :
    (decrementSet s).fst.length = if 0 ∈ s then s.length - 1 else s.length := by
  unfold decrementSet
  by_cases h : 0 ∈ s
  · simp [h, List.length_erase_of_mem h]
  · simp [h]

/-- One step of System 4 per `TM23Proof.pdf` p. 34, `system4.pl`.
    Five rules dispatched on (state, kind of elems[active]).
    Returns `none` if `active >= elems.length` (halt). -/
def System4.step (cfg : System4Config) : Option System4Config :=
  if h_bound : cfg.active < cfg.elems.length then
    match cfg.elems.get ⟨cfg.active, h_bound⟩, cfg.state with
    | System4Elem.star, System4State.A =>
        -- Rule 2: star in A - remove the star, state->B (active stays).
        some { elems := cfg.elems.eraseIdx cfg.active
               active := cfg.active
               state := System4State.B }
    | System4Elem.set _, System4State.A =>
        -- Rule 1: set in A - active--; if at 0, state->B.
        if cfg.active = 0 then
          some { elems := cfg.elems, active := 0, state := System4State.B }
        else
          some { elems := cfg.elems
                 active := cfg.active - 1
                 state := System4State.A }
    | System4Elem.set s, _ =>
        -- Rule 3: set in B/C - decrement, toggle state if 0 was present.
        let (newSet, hadZero) := decrementSet s
        let newState :=
          if hadZero then
            match cfg.state with
            | System4State.B => System4State.C
            | System4State.C => System4State.B
            | System4State.A => cfg.state  -- handled by case 1; unreachable
          else cfg.state
        some { elems := cfg.elems.set cfg.active (System4Elem.set newSet)
               active := cfg.active + 1
               state := newState }
    | System4Elem.star, System4State.B =>
        -- Rule 4: star in B - remove the star, active--, state->A.
        if cfg.active = 0 then none
        else
          some { elems := cfg.elems.eraseIdx cfg.active
                 active := cfg.active - 1
                 state := System4State.A }
    | System4Elem.star, System4State.C =>
        -- Rule 5: star in C - active++, toggle membership of `1` in
        -- elems[active] (which must be a set).
        let newActive := cfg.active + 1
        if h_new : newActive < cfg.elems.length then
          match cfg.elems.get ⟨newActive, h_new⟩ with
          | System4Elem.set s =>
              some { elems := cfg.elems.set newActive
                       (System4Elem.set (xorInsert 1 s))
                     active := newActive
                     state := System4State.C }
          | System4Elem.star => none  -- adjacent stars: shouldn't happen by
                                       -- the construction (PDF p. 35)
        else none
  else none

/-- Run System 4 for exactly `m` steps; halts if any intermediate step
    returns `none`. -/
def System4.nSteps (cfg : System4Config) : Nat → Option System4Config
  | 0 => some cfg
  | m + 1 =>
    match System4.step cfg with
    | none => none
    | some cfg' => System4.nSteps cfg' m

/-- 0-step iteration is the identity. -/
@[simp] theorem System4.nSteps_zero (cfg : System4Config) :
    System4.nSteps cfg 0 = some cfg := rfl

/-- 1-step iteration is `System4.step`. -/
theorem System4.nSteps_one (cfg : System4Config) :
    System4.nSteps cfg 1 = System4.step cfg := by
  show (match System4.step cfg with
        | none => none
        | some cfg' => System4.nSteps cfg' 0) = System4.step cfg
  cases System4.step cfg <;> rfl

/-- Additive composition:
    `nSteps cfg (n + m) = nSteps cfg n >>= (fun c => nSteps c m)`. -/
theorem System4.nSteps_add (cfg : System4Config) (n m : Nat) :
    System4.nSteps cfg (n + m)
      = (System4.nSteps cfg n).bind (fun c => System4.nSteps c m) := by
  induction n generalizing cfg with
  | zero => simp [System4.nSteps]
  | succ n ih =>
    rw [Nat.succ_add]
    show (match System4.step cfg with
          | none => none
          | some c => System4.nSteps c (n + m))
        = (match System4.step cfg with
            | none => none
            | some c => System4.nSteps c n).bind
          (fun c => System4.nSteps c m)
    cases System4.step cfg with
    | none => rfl
    | some c => exact ih c

/-- Direct-recursion form: `nSteps cfg (n+1) = step cfg >>= (fun c => nSteps c n)`.
    Definitional, but stated explicitly for ergonomic use.
    Mirrors `System5.nSteps_succ`. -/
theorem System4.nSteps_succ (cfg : System4Config) (n : Nat) :
    System4.nSteps cfg (n + 1)
      = (System4.step cfg).bind (fun c => System4.nSteps c n) := by
  rw [Nat.add_comm, System4.nSteps_add, System4.nSteps_one]

/-- **Sanity check** against PDF p. 34/35 trace.  Initial config from
    `system4.pl 0,6,8 "" _ B 3,4 _ 8 11,20`.  After step 1 (rule 3:
    set in B, decrement `[3,4]` -> `[2,3]`, no `0` so no state toggle,
    `active++`), state moves from active=3 (`{3,4}`) to active=4 (`*`).

    Per PDF: `0,6,8 "" _ B 3,4 _ 8 11,20` -> `0,6,8 "" _ 2,3 B _ 8 11,20`. -/
example :
    System4.step { elems := [System4Elem.set [0, 6, 8], System4Elem.set [],
                              System4Elem.star, System4Elem.set [3, 4],
                              System4Elem.star, System4Elem.set [8],
                              System4Elem.set [11, 20]],
                   active := 3,
                   state := System4State.B }
    = some { elems := [System4Elem.set [0, 6, 8], System4Elem.set [],
                       System4Elem.star, System4Elem.set [2, 3],
                       System4Elem.star, System4Elem.set [8],
                       System4Elem.set [11, 20]],
             active := 4,
             state := System4State.B } := by
  decide

/-- 2 steps from same initial config: step 1 (rule 3, set in B) then
    step 2 (rule 4, star in B).  After step 2: star removed, active--,
    state->A.  PDF p. 35 trace continues with the new active = 3 (= `{2,3}`). -/
example :
    System4.nSteps
      { elems := [System4Elem.set [0, 6, 8], System4Elem.set [],
                  System4Elem.star, System4Elem.set [3, 4],
                  System4Elem.star, System4Elem.set [8],
                  System4Elem.set [11, 20]],
        active := 3,
        state := System4State.B } 2
    = some { elems := [System4Elem.set [0, 6, 8], System4Elem.set [],
                       System4Elem.star, System4Elem.set [2, 3],
                       System4Elem.set [8], System4Elem.set [11, 20]],
             active := 3,
             state := System4State.A } := by
  decide

/-- A System 4 cfg halts iff `nSteps` returns `none` for some budget. -/
def System4.Halts (cfg : System4Config) : Prop :=
  ∃ n, System4.nSteps cfg n = none

/-- `System4.step` returns `none` whenever `active` is out of bounds. -/
theorem System4.step_none_of_active_oob (cfg : System4Config)
    (h : cfg.active ≥ cfg.elems.length) :
    System4.step cfg = none := by
  unfold System4.step
  rw [dif_neg (Nat.not_lt.mpr h)]

/-- Trivial halting witness: `active` out of bounds => halts in one step. -/
theorem System4.Halts_of_active_oob (cfg : System4Config)
    (h : cfg.active ≥ cfg.elems.length) :
    System4.Halts cfg :=
  ⟨1, by rw [System4.nSteps_one]; exact System4.step_none_of_active_oob cfg h⟩

/-- Trivial halting witness: empty `elems` => halts in one step. -/
theorem System4.Halts_of_empty_elems (cfg : System4Config) (h : cfg.elems = []) :
    System4.Halts cfg := by
  apply System4.Halts_of_active_oob
  simp [h]

/-- **System4 Halts step-pred**: backward Halts propagation under stepping. -/
theorem System4_Halts_step_pred
    (cfg cfg' : System4Config) (h_step : System4.step cfg = some cfg')
    (h : System4.Halts cfg') :
    System4.Halts cfg := by
  obtain ⟨n, h_n⟩ := h
  refine ⟨n + 1, ?_⟩
  rw [System4.nSteps_succ, h_step]
  exact h_n

/-- **System4 Halts step-succ**: forward Halts propagation. -/
theorem System4_Halts_step_succ
    (cfg cfg' : System4Config) (h_step : System4.step cfg = some cfg')
    (h : System4.Halts cfg) :
    System4.Halts cfg' := by
  obtain ⟨n, h_n⟩ := h
  cases n with
  | zero =>
    simp [System4.nSteps_zero] at h_n
  | succ k =>
    rw [System4.nSteps_succ, h_step] at h_n
    exact ⟨k, h_n⟩

/-- **System4 Halts step-iff**: biconditional. -/
theorem System4_Halts_step_iff
    (cfg cfg' : System4Config) (h_step : System4.step cfg = some cfg') :
    System4.Halts cfg ↔ System4.Halts cfg' :=
  ⟨System4_Halts_step_succ cfg cfg' h_step, System4_Halts_step_pred cfg cfg' h_step⟩

/-- **System4 Halts nSteps-pred**: backward via multi-step. -/
theorem System4_Halts_nSteps_pred
    (cfg : System4Config) (n : Nat) (r : System4Config)
    (h_n : System4.nSteps cfg n = some r) (h : System4.Halts r) :
    System4.Halts cfg := by
  induction n generalizing cfg with
  | zero =>
    rw [System4.nSteps_zero] at h_n
    injection h_n with h_eq
    rw [h_eq]
    exact h
  | succ k ih =>
    rw [System4.nSteps_succ] at h_n
    cases h_step : System4.step cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      simp at h_n
      exact System4_Halts_step_pred cfg cfg₁ h_step (ih cfg₁ h_n)

/-- **System4 Halts nSteps-succ**: forward via multi-step. -/
theorem System4_Halts_nSteps_succ
    (cfg : System4Config) (n : Nat) (r : System4Config)
    (h_n : System4.nSteps cfg n = some r) (h : System4.Halts cfg) :
    System4.Halts r := by
  induction n generalizing cfg with
  | zero =>
    rw [System4.nSteps_zero] at h_n
    injection h_n with h_eq
    rw [← h_eq]
    exact h
  | succ k ih =>
    rw [System4.nSteps_succ] at h_n
    cases h_step : System4.step cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      simp at h_n
      exact ih cfg₁ h_n (System4_Halts_step_succ cfg cfg₁ h_step h)

/-- **System4 Halts nSteps-iff**: biconditional. -/
theorem System4_Halts_nSteps_iff
    (cfg : System4Config) (n : Nat) (r : System4Config)
    (h_n : System4.nSteps cfg n = some r) :
    System4.Halts cfg ↔ System4.Halts r :=
  ⟨System4_Halts_nSteps_succ cfg n r h_n, System4_Halts_nSteps_pred cfg n r h_n⟩

/-- If `step cfg = none`, then `cfg` halts in 1 step. -/
theorem System4.Halts_of_step_none (cfg : System4Config)
    (h : System4.step cfg = none) :
    System4.Halts cfg :=
  ⟨1, by rw [System4.nSteps_one]; exact h⟩

/-- Contrapositive of `System4.Halts_of_step_none` - if `cfg` does NOT halt,
    then `step cfg` is `some`.  Mirrors the System 5 version. -/
theorem System4_not_Halts_imp_step_some (cfg : System4Config)
    (h : ¬ System4.Halts cfg) :
    ∃ cfg', System4.step cfg = some cfg' := by
  cases h_step : System4.step cfg with
  | none =>
    exfalso
    apply h
    exact System4.Halts_of_step_none cfg h_step
  | some cfg' => exact ⟨cfg', rfl⟩

/-- Contrapositive of `System4_Halts_step_pred` - non-halt propagates forward
    through step. -/
theorem System4_not_Halts_step_succ
    (cfg cfg' : System4Config) (h_step : System4.step cfg = some cfg')
    (h : ¬ System4.Halts cfg) :
    ¬ System4.Halts cfg' :=
  fun h_halt => h (System4_Halts_step_pred cfg cfg' h_step h_halt)

/-- **System4 not-Halts nSteps-succ**: nSteps version of
    `System4_not_Halts_step_succ`. -/
theorem System4_not_Halts_nSteps_succ
    (cfg : System4Config) (n : Nat) (r : System4Config)
    (h_n : System4.nSteps cfg n = some r) (h : ¬ System4.Halts cfg) :
    ¬ System4.Halts r :=
  fun h_halt => h (System4_Halts_nSteps_pred cfg n r h_n h_halt)

/-- **System4 self-loop nSteps stays at cfg**: if `step cfg = some cfg`,
    then `nSteps cfg n = some cfg` for any n. -/
theorem System4_self_loop_nSteps_self
    (cfg : System4Config) (h_self : System4.step cfg = some cfg) (n : Nat) :
    System4.nSteps cfg n = some cfg := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [System4.nSteps_succ, h_self]
    simpa using ih

/-- **System4 self-loop => not-Halts**. -/
theorem System4_self_loop_not_halts
    (cfg : System4Config) (h_self : System4.step cfg = some cfg) :
    ¬ System4.Halts cfg := by
  intro ⟨n, h_n⟩
  rw [System4_self_loop_nSteps_self cfg h_self n] at h_n
  cases h_n

/-- **System4 step-none nSteps succ eq none**. -/
theorem System4_step_none_nSteps_succ_eq_none
    (cfg : System4Config) (h : System4.step cfg = none) (n : Nat) :
    System4.nSteps cfg (n + 1) = none := by
  rw [System4.nSteps_succ, h]
  rfl

/-- **System4 nSteps past step-none = none**. -/
theorem System4_nSteps_past_step_none_eq_none
    (cfg : System4Config) (n : Nat) (result : System4Config)
    (h_n : System4.nSteps cfg n = some result) (h_step : System4.step result = none)
    (k : Nat) (h_k : k ≥ 1) :
    System4.nSteps cfg (n + k) = none := by
  rw [System4.nSteps_add, h_n]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simpa using System4_step_none_nSteps_succ_eq_none result h_step m

/-- **System4 nSteps intermediate retrieval**. -/
theorem System4_nSteps_intermediate
    (cfg r₁ r₂ : System4Config) (n₁ n₂ : Nat) (h_le : n₁ ≤ n₂)
    (h₁ : System4.nSteps cfg n₁ = some r₁)
    (h₂ : System4.nSteps cfg n₂ = some r₂) :
    System4.nSteps r₁ (n₂ - n₁) = some r₂ := by
  have h_sum : n₁ + (n₂ - n₁) = n₂ := by omega
  rw [← h_sum, System4.nSteps_add, h₁] at h₂
  exact h₂

/-- **System4 step-none implies Halts**. -/
theorem System4_step_none_imp_Halts (cfg : System4Config)
    (h : System4.step cfg = none) :
    System4.Halts cfg :=
  ⟨1, by rw [System4.nSteps_one]; exact h⟩

/-- **System4 nSteps intermediate Halts retrieval**. -/
theorem System4_nSteps_intermediate_Halts
    (cfg r₁ r₂ : System4Config) (n₁ n₂ : Nat) (h_le : n₁ ≤ n₂)
    (h₁ : System4.nSteps cfg n₁ = some r₁)
    (h₂ : System4.nSteps cfg n₂ = some r₂) (h_step_r₂ : System4.step r₂ = none) :
    System4.Halts r₁ :=
  System4_Halts_nSteps_pred r₁ (n₂ - n₁) r₂
    (System4_nSteps_intermediate cfg r₁ r₂ n₁ n₂ h_le h₁ h₂)
    (System4_step_none_imp_Halts r₂ h_step_r₂)

/-- **System4 periodic-orbit nSteps stays at cfg modulo k iterations**. -/
theorem System4_periodic_nSteps_iter
    (cfg : System4Config) (p : Nat)
    (h_period : System4.nSteps cfg p = some cfg) (k : Nat) :
    System4.nSteps cfg (k * p) = some cfg := by
  induction k with
  | zero => rw [Nat.zero_mul]; rfl
  | succ k ih =>
    rw [Nat.succ_mul, System4.nSteps_add, ih]
    simpa using h_period

/-- Backward direction of the step-none witness characterisation - if some
    intermediate cfg `r` reached after `k` steps has `step r = none`, then the
    original cfg halts.  Mirrors `System5` version. -/
theorem System4_Halts_of_exists_step_none
    (cfg : System4Config)
    (h : ∃ k r, System4.nSteps cfg k = some r ∧ System4.step r = none) :
    System4.Halts cfg := by
  obtain ⟨k, r, h_n, h_step⟩ := h
  exact System4_Halts_nSteps_pred cfg k r h_n
    (System4_step_none_imp_Halts r h_step)

/-- **System4 nSteps compose**: chain `nSteps` trajectories. -/
theorem System4_nSteps_some_compose
    (cfg mid : System4Config) (n m : Nat) (result : System4Config)
    (h_n : System4.nSteps cfg n = some mid)
    (h_m : System4.nSteps mid m = some result) :
    System4.nSteps cfg (n + m) = some result := by
  rw [System4.nSteps_add, h_n]
  exact h_m

/-- **System4 step-none witness extractor**: from `System4.Halts cfg`,
    extract `(k, r)` with `nSteps cfg k = some r /\ System4.step r = none`. -/
theorem System4_Halts_extract_step_none_witness
    (cfg : System4Config) (h : System4.Halts cfg) :
    ∃ k r, System4.nSteps cfg k = some r ∧ System4.step r = none := by
  obtain ⟨N, hN⟩ := h
  rcases find_min_or_none (fun n => System4.nSteps cfg n = none) N with
    ⟨n, _h_le, h_pn, h_min⟩ | h_none
  · cases n with
    | zero =>
      simp [System4.nSteps_zero] at h_pn
    | succ k =>
      cases h_k : System4.nSteps cfg k with
      | none => exact absurd h_k (h_min k (Nat.lt_succ_self k))
      | some r =>
        refine ⟨k, r, h_k, ?_⟩
        have h_eq : System4.nSteps cfg (k + 1) = System4.step r := by
          rw [System4.nSteps_add, h_k]
          exact System4.nSteps_one r
        rw [h_eq] at h_pn
        exact h_pn
  · exact absurd hN (h_none N (Nat.le_refl _))

/-- **System4 periodic orbit => not-Halts**. -/
theorem System4_periodic_not_halts
    (cfg : System4Config) (p : Nat) (h_pos : p ≥ 1)
    (h_period : System4.nSteps cfg p = some cfg) :
    ¬ System4.Halts cfg := by
  intro h_halts
  obtain ⟨N, r, h_n, h_step_none⟩ := System4_Halts_extract_step_none_witness cfg h_halts
  have h_iter := System4_periodic_nSteps_iter cfg p h_period (N + 1)
  have h_ge : (N + 1) * p ≥ N + 1 := by
    have : (N + 1) * 1 ≤ (N + 1) * p := Nat.mul_le_mul_left _ h_pos
    omega
  obtain ⟨j, hj_pos, h_eq⟩ : ∃ j, j ≥ 1 ∧ (N + 1) * p = N + j :=
    ⟨(N + 1) * p - N, by omega, by omega⟩
  rw [h_eq] at h_iter
  rw [System4_nSteps_past_step_none_eq_none cfg N r h_n h_step_none j hj_pos]
    at h_iter
  cases h_iter

/-- Biconditional iff form. -/
theorem System4_Halts_iff_exists_step_none_witness (cfg : System4Config) :
    System4.Halts cfg ↔
    ∃ k r, System4.nSteps cfg k = some r ∧ System4.step r = none :=
  ⟨System4_Halts_extract_step_none_witness cfg,
   System4_Halts_of_exists_step_none cfg⟩

/-- Contrapositive of `System4_periodic_not_halts`. -/
theorem System4_no_period_of_Halts
    (cfg : System4Config) (h : System4.Halts cfg)
    (p : Nat) (h_pos : p ≥ 1) :
    System4.nSteps cfg p ≠ some cfg :=
  fun h_period => System4_periodic_not_halts cfg p h_pos h_period h

/-- **System4 -> BiTM step-to-nSteps emulation lifting**: System4 ->
    tm analog of `step_to_nSteps_emulation_system5_to_tm`.  Given
    per-step System4 -> tm emulator, lift to multi-step. -/
theorem step_to_nSteps_emulation_system4_to_tm
    (tm : Machine) (encode : System4Config → Config)
    (h_emulate : ∀ cfg cfg', System4.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (encode cfg) n = some (encode cfg'))
    (cfg : System4Config) (k : Nat) (result : System4Config)
    (h_steps : System4.nSteps cfg k = some result) :
    ∃ m, nSteps tm (encode cfg) m = some (encode result) := by
  induction k generalizing cfg with
  | zero =>
    rw [System4.nSteps_zero] at h_steps
    injection h_steps with h_eq
    refine ⟨0, ?_⟩
    rw [h_eq]
    rfl
  | succ k ih =>
    rw [System4.nSteps_succ] at h_steps
    cases h_step : System4.step cfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      simp at h_steps
      obtain ⟨n, _hn_pos, h_n⟩ := h_emulate cfg cfg₁ h_step
      obtain ⟨m', h_m'⟩ := ih cfg₁ h_steps
      exact ⟨n + m',
        BiTM_nSteps_some_compose tm (encode cfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩

/-- **System4 -> BiTM halt-preservation under step emulation**.
    Composes step-to-nSteps lifting + System4 step-none witness
    extractor + `BiTM_Halts_nSteps_pred`. -/
theorem system4Halts_imp_tmHalts_under_step_emulation
    (tm : Machine) (encode : System4Config → Config)
    (h_step_emulate : ∀ cfg cfg', System4.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (encode cfg) n = some (encode cfg'))
    (h_halt_preserve : ∀ cfg, System4.step cfg = none → Halts tm (encode cfg))
    (cfg : System4Config) (h : System4.Halts cfg) :
    Halts tm (encode cfg) := by
  obtain ⟨k, r, h_n, h_step_none⟩ := System4_Halts_extract_step_none_witness cfg h
  obtain ⟨m, h_m⟩ := step_to_nSteps_emulation_system4_to_tm
    tm encode h_step_emulate cfg k r h_n
  exact BiTM_Halts_nSteps_pred tm (encode cfg) m (encode r) h_m
    (h_halt_preserve r h_step_none)

/-- Contrapositive of `system4Halts_imp_tmHalts_under_step_emulation`. -/
theorem system4_not_Halts_of_tm_not_Halts
    (tm : Machine) (encode : System4Config → Config)
    (h_step_emulate : ∀ cfg cfg', System4.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (encode cfg) n = some (encode cfg'))
    (h_halt_preserve : ∀ cfg, System4.step cfg = none → Halts tm (encode cfg))
    (cfg : System4Config) (h : ¬ Halts tm (encode cfg)) :
    ¬ System4.Halts cfg :=
  fun h_halts => h (system4Halts_imp_tmHalts_under_step_emulation tm encode
    h_step_emulate h_halt_preserve cfg h_halts)

/-- Any halting System4 cfg is either at halt position (`step cfg = none`) or
    steps to another halting cfg. -/
theorem System4_Halts_step_decompose
    (cfg : System4Config) (h : System4.Halts cfg) :
    System4.step cfg = none ∨
    ∃ cfg', System4.step cfg = some cfg' ∧ System4.Halts cfg' := by
  cases h_step : System4.step cfg with
  | none => left; rfl
  | some cfg' =>
    right
    exact ⟨cfg', rfl, (System4_Halts_step_iff cfg cfg' h_step).mp h⟩

/-- When `step` is known to succeed, the step branch is forced. -/
theorem System4_Halts_step_decompose_some
    (cfg cfg' : System4Config) (h_step : System4.step cfg = some cfg')
    (h_halts : System4.Halts cfg) :
    System4.Halts cfg' := by
  rcases System4_Halts_step_decompose cfg h_halts with h_none | ⟨cfg'', h_step', h_halts'⟩
  · rw [h_none] at h_step; cases h_step
  · rw [h_step] at h_step'
    have heq : cfg' = cfg'' := by injection h_step'
    rw [heq]; exact h_halts'

/-- Strong induction over halting System4 cfgs.  Halt base is `step cfg =
    none` (System4 has multiple halt conditions: active OOB, rule 4 with
    active=0, adjacent stars in rule 5). -/
theorem System4_Halts_induction (P : System4Config → Prop)
    (h_halt : ∀ cfg, System4.step cfg = none → P cfg)
    (h_back : ∀ cfg cfg', System4.step cfg = some cfg' →
              System4.Halts cfg' → P cfg' → P cfg)
    (cfg : System4Config) (h : System4.Halts cfg) : P cfg := by
  obtain ⟨n, h_n⟩ := h
  induction n generalizing cfg with
  | zero => simp [System4.nSteps] at h_n
  | succ m ih =>
    cases h_step : System4.step cfg with
    | none => exact h_halt cfg h_step
    | some cfg' =>
      have h_n' : System4.nSteps cfg' m = none := by
        rw [System4.nSteps_succ, h_step] at h_n
        exact h_n
      have h_he' : System4.Halts cfg' := ⟨m, h_n'⟩
      exact h_back cfg cfg' h_step h_he' (ih cfg' h_n')

/-- **System4 -> BiTM step-to-nSteps emulation positive bound**.
    Required for chain composition. -/
theorem step_to_nSteps_emulation_system4_to_tm_pos
    (tm : Machine) (encode : System4Config → Config)
    (h_emulate : ∀ cfg cfg', System4.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (encode cfg) n = some (encode cfg'))
    (cfg : System4Config) (k : Nat) (h_pos : k ≥ 1) (result : System4Config)
    (h_steps : System4.nSteps cfg k = some result) :
    ∃ m, m ≥ 1 ∧ nSteps tm (encode cfg) m = some (encode result) := by
  cases k with
  | zero => omega
  | succ k =>
    rw [System4.nSteps_succ] at h_steps
    cases h_step : System4.step cfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      simp at h_steps
      obtain ⟨n, hn_pos, h_n⟩ := h_emulate cfg cfg₁ h_step
      obtain ⟨m', h_m'⟩ := step_to_nSteps_emulation_system4_to_tm
        tm encode h_emulate cfg₁ k result h_steps
      exact ⟨n + m', by omega,
        BiTM_nSteps_some_compose tm (encode cfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩

/-- A halting System 4 cfg has all later `nSteps` equal to `none`.
    Loose bound `N = n` (the halting witness step count).  Proof:
    `System4.nSteps_add` plus `none.bind = none`. -/
theorem System4_Halts_imp_nSteps_eventually_none (cfg : System4Config)
    (h : System4.Halts cfg) :
    ∃ N, ∀ k, k > N → System4.nSteps cfg k = none := by
  obtain ⟨n, h_n⟩ := h
  refine ⟨n, ?_⟩
  intro k h_k
  have h_split : k = n + (k - n) := by omega
  rw [h_split, System4.nSteps_add, h_n]
  rfl


/-- If `nSteps cfg n = none`, then some intermediate cfg at step `k < n` has
    `step = none`.  Building block for `System4_Halts_iff_exact_step_witness`. -/
theorem System4_nSteps_none_decompose (cfg : System4Config) (n : Nat)
    (h : System4.nSteps cfg n = none) :
    ∃ k < n, ∃ cfg', System4.nSteps cfg k = some cfg' ∧ System4.step cfg' = none := by
  induction n generalizing cfg with
  | zero => simp [System4.nSteps] at h
  | succ m ih =>
    rw [System4.nSteps_succ] at h
    cases h_step : System4.step cfg with
    | none => refine ⟨0, by omega, cfg, rfl, h_step⟩
    | some cfg' =>
      rw [h_step] at h
      simp at h
      obtain ⟨k', h_k', cfg_h, h_n', h_step_h⟩ := ih cfg' h
      refine ⟨k' + 1, by omega, cfg_h, ?_, h_step_h⟩
      rw [System4.nSteps_succ, h_step]
      exact h_n'

/-- `System4.Halts cfg <-> exists exact step-none witness with
    eventually-none beyond`.  Completes the
    exact-step-witness biconditional family across all five
    systems (BiTM/CTS/Tag/System5/System4). -/
theorem System4_Halts_iff_exact_step_witness (cfg : System4Config) :
    System4.Halts cfg ↔
    ∃ N result, System4.nSteps cfg N = some result ∧
                System4.step result = none ∧
                ∀ k, k > N → System4.nSteps cfg k = none := by
  constructor
  · rintro ⟨n, h_n⟩
    obtain ⟨N, _, result, h_step, h_halt⟩ :=
      System4_nSteps_none_decompose cfg n h_n
    refine ⟨N, result, h_step, h_halt, ?_⟩
    intro k h_k
    have h_split : k = N + (k - N) := by omega
    rw [h_split, System4.nSteps_add, h_step]
    cases h_kN : k - N with
    | zero => omega
    | succ j =>
      show System4.nSteps result (j + 1) = none
      rw [System4.nSteps_succ, h_halt]; rfl
  · rintro ⟨N, result, h_n, h_halt, _⟩
    refine ⟨N + 1, ?_⟩
    rw [System4.nSteps_add, h_n]
    show System4.nSteps result 1 = none
    rw [System4.nSteps_succ, h_halt]; rfl

/-- System 4 analog of `System5_Halts_succ_boundary`.  From `System4.Halts
    cfg`, extracts the exact halt boundary - there exists `n` with
    `nSteps cfg n = some result /\ nSteps cfg (n+1) = none`.  Direct
    via `_Halts_iff_exact_step_witness` (forward direction): the
    exact halt step `N` produces `some result`, and `N + 1 > N` lies
    in the eventually-none zone. -/
theorem System4_Halts_succ_boundary (cfg : System4Config)
    (h : System4.Halts cfg) :
    ∃ n result, System4.nSteps cfg n = some result
              ∧ System4.nSteps cfg (n + 1) = none := by
  obtain ⟨N, result, h_n, _h_halt, h_eventual⟩ :=
    (System4_Halts_iff_exact_step_witness cfg).mp h
  exact ⟨N, result, h_n, h_eventual (N + 1) (by omega)⟩

/-- System4 uniqueness analog. -/
theorem System4_Halts_exact_step_form_unique (cfg : System4Config)
    (N₁ N₂ : Nat) (result₁ result₂ : System4Config)
    (h₁_n : System4.nSteps cfg N₁ = some result₁)
    (h₁_eventual : ∀ k, k > N₁ → System4.nSteps cfg k = none)
    (h₂_n : System4.nSteps cfg N₂ = some result₂)
    (h₂_eventual : ∀ k, k > N₂ → System4.nSteps cfg k = none) :
    N₁ = N₂ := by
  rcases Nat.lt_or_ge N₁ N₂ with h_lt | h_ge
  · have h_none := h₁_eventual N₂ h_lt
    rw [h_none] at h₂_n; cases h₂_n
  · rcases Nat.lt_or_ge N₂ N₁ with h_lt' | h_ge'
    · have h_none := h₂_eventual N₁ h_lt'
      rw [h_none] at h₁_n; cases h₁_n
    · omega
/-- System4 has no clean step-none halt criterion (multiple paths to step =
    none), so the biconditional uses `System4.step cfg = none` directly:
    `System4.Halts cfg <-> System4.step cfg = none \/ (exists cfg',
    System4.step cfg = some cfg' /\ System4.Halts cfg')`. Completes the
    Halts-iff-step-or-halt biconditional family across
    BiTM/CTS/Tag/System5/System4. -/
theorem System4_Halts_iff_step_none_or_step (cfg : System4Config) :
    System4.Halts cfg ↔ System4.step cfg = none ∨
                       ∃ cfg', System4.step cfg = some cfg' ∧
                               System4.Halts cfg' := by
  constructor
  · exact System4_Halts_step_decompose cfg
  · rintro (h_none | ⟨cfg', h_step, h_halts⟩)
    · refine ⟨1, ?_⟩
      rw [System4.nSteps_succ, h_none]
      rfl
    · exact System4_Halts_step_pred cfg cfg' h_step h_halts
/-- System4 analog. -/
theorem System4_Halts_first_none (cfg : System4Config)
    (h : System4.Halts cfg) :
    ∃ n, System4.nSteps cfg n = none ∧ ∀ m < n, System4.nSteps cfg m ≠ none := by
  obtain ⟨N, hN⟩ := h
  rcases find_min_or_none (fun n => System4.nSteps cfg n = none) N with
    ⟨k, _h_le, h_pk, h_min⟩ | h_none
  · exact ⟨k, h_pk, h_min⟩
  · exact absurd hN (h_none N (Nat.le_refl _))
/-- System4 analog - direct contrapositive of existing `System4_periodic_not_halts`. -/
theorem System4_Halts_no_period
    (cfg : System4Config) (h : System4.Halts cfg)
    (p : Nat) (h_pos : p ≥ 1) :
    System4.nSteps cfg p ≠ some cfg :=
  fun h_period => System4_periodic_not_halts cfg p h_pos h_period h
/-- System4 analog. -/
theorem System4_not_Halts_iff_nSteps_always_some (cfg : System4Config) :
    ¬ System4.Halts cfg ↔ ∀ n, ∃ result, System4.nSteps cfg n = some result := by
  constructor
  · intro h_not_halts n
    cases h_n : System4.nSteps cfg n with
    | none => exact absurd ⟨n, h_n⟩ h_not_halts
    | some r => exact ⟨r, rfl⟩
  · intro h_all ⟨n, h_n⟩
    obtain ⟨r, h_r⟩ := h_all n
    rw [h_r] at h_n; cases h_n
/-- System4 analog. -/
theorem System4_nSteps_halt_unique (cfg : System4Config)
    (n₁ n₂ : Nat) (r₁ r₂ : System4Config)
    (h₁ : System4.nSteps cfg n₁ = some r₁) (h_step₁ : System4.step r₁ = none)
    (h₂ : System4.nSteps cfg n₂ = some r₂) (h_step₂ : System4.step r₂ = none) :
    n₁ = n₂ := by
  rcases Nat.lt_or_ge n₁ n₂ with h_lt | h_ge
  · obtain ⟨k, hk_pos, rfl⟩ : ∃ k, k ≥ 1 ∧ n₂ = n₁ + k :=
      ⟨n₂ - n₁, by omega, by omega⟩
    rw [System4_nSteps_past_step_none_eq_none cfg n₁ r₁ h₁ h_step₁ k hk_pos] at h₂
    cases h₂
  · rcases Nat.lt_or_eq_of_le h_ge with h_lt | h_eq
    · obtain ⟨k, hk_pos, rfl⟩ : ∃ k, k ≥ 1 ∧ n₁ = n₂ + k :=
        ⟨n₁ - n₂, by omega, by omega⟩
      rw [System4_nSteps_past_step_none_eq_none cfg n₂ r₂ h₂ h_step₂ k hk_pos] at h₁
      cases h₁
    · exact h_eq.symm

/-! ## Well-formedness of a System 4 tape -/

/-- `true` exactly on a star. -/
def System4Elem.isStar : System4Elem -> Bool
  | System4Elem.star => true
  | System4Elem.set _ => false

/-- `true` on a star, and on a set that has no duplicates. -/
def System4Elem.setNodup : System4Elem -> Bool
  | System4Elem.star => true
  | System4Elem.set s => decide s.Nodup

/-- `true` when the first tape element is not a star. -/
def headNotStar (l : List System4Elem) : Bool :=
  match l.head? with
  | none => true
  | some e => !e.isStar

/-- `true` when no two consecutive tape elements are both stars. -/
def noAdjacentStars : List System4Elem -> Bool
  | [] => true
  | e :: rest =>
      (match rest.head? with
       | some c => !(e.isStar && c.isStar)
       | none => true) && noAdjacentStars rest

/-- A well-formed System 4 tape: the leftmost element is a set, no two stars
    are adjacent, and every set has no duplicates.  `s52s4.pl` emits exactly
    such tapes; rule 5 (star in state C) is only defined on them, and the
    parity semantics of the sets needs the `Nodup` clause. -/
def System4Config.WellFormed (cfg : System4Config) : Prop :=
  headNotStar cfg.elems = true
    ∧ noAdjacentStars cfg.elems = true
    ∧ cfg.elems.all System4Elem.setNodup = true

/-- `WellFormed` is a conjunction of Boolean equations, hence decidable. -/
instance System4Config.instDecidableWellFormed (cfg : System4Config) :
    Decidable cfg.WellFormed := by
  unfold System4Config.WellFormed
  infer_instance

/-- Tail of a tape with no adjacent stars has no adjacent stars. -/
theorem noAdjacentStars_tail (e : System4Elem) (rest : List System4Elem)
    (h : noAdjacentStars (e :: rest) = true) : noAdjacentStars rest = true := by
  simp only [noAdjacentStars, Bool.and_eq_true] at h
  exact h.2

/-- Introduction rule for `noAdjacentStars` on a cons. -/
theorem noAdjacentStars_cons (e : System4Elem) (rest : List System4Elem)
    (h_head : ∀ c, rest.head? = some c → (e.isStar && c.isStar) = false)
    (h_rest : noAdjacentStars rest = true) :
    noAdjacentStars (e :: rest) = true := by
  simp only [noAdjacentStars, Bool.and_eq_true]
  refine ⟨?_, h_rest⟩
  cases h_c : rest.head? with
  | none => rfl
  | some c => simp [h_head c h_c]

/-- Elimination rule for `noAdjacentStars` on a cons. -/
theorem noAdjacentStars_cons_head (e c : System4Elem) (rest : List System4Elem)
    (h : noAdjacentStars (e :: rest) = true) (h_c : rest.head? = some c) :
    (e.isStar && c.isStar) = false := by
  simp only [noAdjacentStars, Bool.and_eq_true] at h
  have h1 := h.1
  rw [h_c] at h1
  rwa [Bool.not_eq_true'] at h1

/-- The head of `l.set i x` is either `x` or the head of `l`. -/
theorem head?_set (l : List System4Elem) (i : Nat) (x c : System4Elem)
    (h : (l.set i x).head? = some c) : c = x ∨ l.head? = some c := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases i with
    | zero => left; simpa using h.symm
    | succ j => right; simpa using h

/-- Replacing a tape element by a non-star keeps stars non-adjacent. -/
theorem noAdjacentStars_set_notStar (l : List System4Elem) (i : Nat)
    (x : System4Elem) (h_x : x.isStar = false) (h : noAdjacentStars l = true) :
    noAdjacentStars (l.set i x) = true := by
  induction l generalizing i with
  | nil => rfl
  | cons e rest ih =>
    cases i with
    | zero =>
      show noAdjacentStars (x :: rest) = true
      exact noAdjacentStars_cons x rest (fun c _ => by simp [h_x])
        (noAdjacentStars_tail e rest h)
    | succ j =>
      show noAdjacentStars (e :: rest.set j x) = true
      refine noAdjacentStars_cons e _ ?_ (ih j (noAdjacentStars_tail e rest h))
      intro c h_c
      rcases head?_set rest j x c h_c with rfl | h_head
      · simp [h_x]
      · exact noAdjacentStars_cons_head e c rest h h_head

/-- Deleting a star keeps stars non-adjacent: its two neighbours are both
    non-stars, so they may be brought together. -/
theorem noAdjacentStars_eraseIdx_star (l : List System4Elem) (i : Nat)
    (e0 : System4Elem) (h_get : l[i]? = some e0) (h_star : e0.isStar = true)
    (h : noAdjacentStars l = true) :
    noAdjacentStars (l.eraseIdx i) = true := by
  induction l generalizing i with
  | nil => rfl
  | cons e rest ih =>
    cases i with
    | zero =>
      show noAdjacentStars rest = true
      exact noAdjacentStars_tail e rest h
    | succ j =>
      show noAdjacentStars (e :: rest.eraseIdx j) = true
      have h_rest : rest[j]? = some e0 := by simpa using h_get
      refine noAdjacentStars_cons e _ ?_
        (ih j h_rest (noAdjacentStars_tail e rest h))
      intro c h_c
      cases rest with
      | nil => simp at h_c
      | cons a rest' =>
        cases j with
        | zero =>
          have h_a : a = e0 := by simpa using h_rest
          have h_ea : (e.isStar && a.isStar) = false :=
            noAdjacentStars_cons_head e a (a :: rest') h rfl
          rw [h_a, h_star, Bool.and_true] at h_ea
          simp [h_ea]
        | succ k =>
          have h_ca : c = a := by simpa using h_c.symm
          rw [h_ca]
          exact noAdjacentStars_cons_head e a (a :: rest') h rfl

/-- Replacing a tape element by a non-star keeps the leftmost element a set. -/
theorem headNotStar_set (l : List System4Elem) (i : Nat) (x : System4Elem)
    (h_x : x.isStar = false) (h : headNotStar l = true) :
    headNotStar (l.set i x) = true := by
  cases l with
  | nil => rfl
  | cons e rest =>
    cases i with
    | zero =>
      show headNotStar (x :: rest) = true
      simp [headNotStar, h_x]
    | succ j =>
      show headNotStar (e :: rest.set j x) = true
      simpa [headNotStar] using h

/-- Deleting a star keeps the leftmost element a set.  The star cannot be at
    index 0, because the leftmost element is a set. -/
theorem headNotStar_eraseIdx_star (l : List System4Elem) (i : Nat)
    (e0 : System4Elem) (h_get : l[i]? = some e0) (h_star : e0.isStar = true)
    (h : headNotStar l = true) :
    headNotStar (l.eraseIdx i) = true := by
  cases l with
  | nil => rfl
  | cons e rest =>
    cases i with
    | zero =>
      exfalso
      have h_e : e = e0 := by simpa using h_get
      have : e.isStar = false := by simpa [headNotStar] using h
      rw [h_e, h_star] at this
      cases this
    | succ j =>
      show headNotStar (e :: rest.eraseIdx j) = true
      simpa [headNotStar] using h

/-- Deleting an element keeps every set duplicate-free. -/
theorem all_setNodup_eraseIdx (l : List System4Elem) (i : Nat)
    (h : l.all System4Elem.setNodup = true) :
    (l.eraseIdx i).all System4Elem.setNodup = true := by
  rw [List.all_eq_true] at h ⊢
  intro x h_x
  exact h x (List.mem_of_mem_eraseIdx h_x)

/-- Replacing an element by a duplicate-free set keeps every set
    duplicate-free. -/
theorem all_setNodup_set (l : List System4Elem) (i : Nat) (x : System4Elem)
    (h_x : x.setNodup = true) (h : l.all System4Elem.setNodup = true) :
    (l.set i x).all System4Elem.setNodup = true := by
  rw [List.all_eq_true] at h ⊢
  intro y h_y
  rcases List.mem_or_eq_of_mem_set h_y with h1 | rfl
  · exact h y h1
  · exact h_x

/-- Decrementing a duplicate-free set leaves it duplicate-free. -/
theorem decrementSet_nodup (s : List Int) (h : s.Nodup) : (decrementSet s).1.Nodup := by
  unfold decrementSet
  by_cases h0 : (0 : Int) ∈ s
  · simp only [h0, if_pos]
    exact nodup_map_sub_one (List.Nodup.erase 0 h)
  · simp only [h0, if_false]
    exact nodup_map_sub_one h

/-- **`System4.step` preserves `System4Config.WellFormed`.**  Rules 1 and 3
    do not move stars; rules 2 and 4 delete a star, whose two neighbours are
    non-stars and so may be brought together; rule 5 only rewrites a set.
    The leftmost element stays a set because a star is never deleted at
    index 0 (rule 4 returns `none` there and rule 2 would need a star at the
    leftmost position, which `headNotStar` forbids). -/
theorem System4_step_wellFormed (cfg cfg' : System4Config)
    (h : cfg.WellFormed) (hs : System4.step cfg = some cfg') : cfg'.WellFormed := by
  obtain ⟨h_head, h_adj, h_nodup⟩ := h
  unfold System4.step at hs
  split at hs
  · rename_i h_bound
    have h_get : cfg.elems[cfg.active]? = some (cfg.elems.get ⟨cfg.active, h_bound⟩) := by
      rw [List.get_eq_getElem]
      exact List.getElem?_eq_getElem h_bound
    have h_mem : cfg.elems.get ⟨cfg.active, h_bound⟩ ∈ cfg.elems := List.get_mem _ _
    split at hs
    · -- rule 2: star in state A
      rename_i heq _
      rw [heq] at h_get
      injection hs with hs
      subst hs
      exact ⟨headNotStar_eraseIdx_star _ _ _ h_get rfl h_head,
             noAdjacentStars_eraseIdx_star _ _ _ h_get rfl h_adj,
             all_setNodup_eraseIdx _ _ h_nodup⟩
    · -- rule 1: set in state A
      split at hs <;> (injection hs with hs; subst hs; exact ⟨h_head, h_adj, h_nodup⟩)
    · -- rule 3: set in state B or C
      rename_i s heq _
      rw [heq] at h_mem
      have h_s : s.Nodup := by
        have := (List.all_eq_true.mp h_nodup) _ h_mem
        simpa [System4Elem.setNodup] using this
      injection hs with hs
      subst hs
      refine ⟨headNotStar_set _ _ _ rfl h_head,
              noAdjacentStars_set_notStar _ _ _ rfl h_adj,
              all_setNodup_set _ _ _ ?_ h_nodup⟩
      simpa [System4Elem.setNodup] using decrementSet_nodup s h_s
    · -- rule 4: star in state B
      rename_i heq _
      rw [heq] at h_get
      split at hs
      · cases hs
      · injection hs with hs
        subst hs
        exact ⟨headNotStar_eraseIdx_star _ _ _ h_get rfl h_head,
               noAdjacentStars_eraseIdx_star _ _ _ h_get rfl h_adj,
               all_setNodup_eraseIdx _ _ h_nodup⟩
    · -- rule 5: star in state C
      rename_i heq _
      dsimp only at hs
      split at hs
      · rename_i h_new
        split at hs
        · rename_i s heq2
          have h_mem2 : cfg.elems.get ⟨cfg.active + 1, h_new⟩ ∈ cfg.elems := List.get_mem _ _
          rw [heq2] at h_mem2
          have h_s : s.Nodup := by
            have := (List.all_eq_true.mp h_nodup) _ h_mem2
            simpa [System4Elem.setNodup] using this
          injection hs with hs
          subst hs
          refine ⟨headNotStar_set _ _ _ rfl h_head,
                  noAdjacentStars_set_notStar _ _ _ rfl h_adj,
                  all_setNodup_set _ _ _ ?_ h_nodup⟩
          simpa [System4Elem.setNodup] using xorInsert_nodup 1 s h_s
        · cases hs
      · cases hs
  · cases hs

/-- `System4Config.WellFormed` is preserved along any number of steps. -/
theorem System4_nSteps_wellFormed (cfg : System4Config) (n : Nat)
    (result : System4Config) (h : cfg.WellFormed)
    (hs : System4.nSteps cfg n = some result) : result.WellFormed := by
  induction n generalizing cfg with
  | zero =>
    rw [System4.nSteps_zero] at hs
    injection hs with h_eq
    rw [← h_eq]; exact h
  | succ k ih =>
    rw [System4.nSteps_succ] at hs
    cases h_step : System4.step cfg with
    | none => rw [h_step] at hs; cases hs
    | some cfg₁ =>
      rw [h_step] at hs
      simp only [Option.bind_some] at hs
      exact ih cfg₁ (System4_step_wellFormed cfg cfg₁ h h_step) hs

end BiTM
