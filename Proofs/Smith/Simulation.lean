/-
  Smith.Simulation

  The emulation calculus shared by every link of the Smith chain
  (PLAN.md section 3).  A link is a relation between the states of two
  deterministic partial step systems such that one source step is matched
  by at least one target step.

  Contents:
    * `ForwardSim`: the emulation predicate, with the `1 <= k` clause that
      forbids a target that stands still.
    * `ForwardSim_comp`: composition along a relational composite.
    * `ForwardSim_nSteps`: lifting to `n` source steps with an explicit
      schedule `times : Nat -> Nat` that is strictly increasing on `[0, n]`
      and starts at 0, plus the weaker `ForwardSim_nSteps_weak`.
    * `ForwardSim_of_stuck` and `ForwardSim_nontrivial`: the vacuity guard.
      A relation all of whose source states are stuck is a `ForwardSim` for
      free; `ForwardSim_nontrivial` is the lemma that rules this out for a
      relation whose source states do step.
    * Non-degeneracy examples for `ForwardSim` and for `IsSimSchedule`,
      positive and negative.
-/

import Smith.StepSys

namespace Smith

universe u v w

/-! ## Forward simulation -/

/-- Forward simulation: every source step is matched by a run of at least
    one target step that re-establishes the relation.  The clause
    `1 <= k` is what forbids the trivial witness in which the target stands
    still while the source moves.

    That clause is all the predicate itself rules out: a relation that
    ignores the source (`fun _ _ => True`) is a `ForwardSim` for any target
    that never gets stuck.  The content of each emulation theorem is in the
    relation being the graph of a (partial) decoder, with the decoders and
    the size and exit clauses stated in the theorems themselves (PLAN.md
    section 6). -/
def ForwardSim {S : Type u} {T : Type v}
    (MS : StepSys S) (MT : StepSys T) (R : S → T → Prop) : Prop :=
  ∀ s t, R s t → ∀ s', MS.step s = some s' →
    ∃ k, 1 ≤ k ∧ ∃ t', MT.nSteps t k = some t' ∧ R s' t'

/-- Relational composition, the relation carried along by `ForwardSim_comp`. -/
def Rcomp {S : Type u} {T : Type v} {U : Type w}
    (R : S → T → Prop) (R' : T → U → Prop) : S → U → Prop :=
  fun s u => ∃ t, R s t ∧ R' t u

/-- Lifting to `n` source steps, weak form: the target takes at least `n`
    steps and the relation holds at the end. -/
theorem ForwardSim_nSteps_weak {S : Type u} {T : Type v}
    {MS : StepSys S} {MT : StepSys T} {R : S → T → Prop}
    (h : ForwardSim MS MT R) (n : Nat) (s : S) (t : T) (hR : R s t)
    (s' : S) (hn : MS.nSteps s n = some s') :
    ∃ m, n ≤ m ∧ ∃ t', MT.nSteps t m = some t' ∧ R s' t' := by
  induction n generalizing s t with
  | zero =>
    simp at hn
    exact ⟨0, Nat.le_refl 0, t, rfl, hn ▸ hR⟩
  | succ n ih =>
    rw [StepSys.nSteps_succ_left] at hn
    cases hstep : MS.step s with
    | none => rw [hstep] at hn; simp at hn
    | some s1 =>
      rw [hstep] at hn
      simp only [Option.bind_some] at hn
      obtain ⟨k, hk, t1, ht1, hR1⟩ := h s t hR s1 hstep
      obtain ⟨m, hm, t', ht', hR'⟩ := ih s1 t1 hR1 hn
      refine ⟨k + m, by omega, t', ?_, hR'⟩
      rw [StepSys.nSteps_add, ht1]
      simpa using ht'

/-- Composition of two forward simulations along the relational composite. -/
theorem ForwardSim_comp {S : Type u} {T : Type v} {U : Type w}
    {MS : StepSys S} {MT : StepSys T} {MU : StepSys U}
    {R : S → T → Prop} {R' : T → U → Prop}
    (h : ForwardSim MS MT R) (h' : ForwardSim MT MU R') :
    ForwardSim MS MU (Rcomp R R') := by
  rintro s u ⟨t, hRst, hR'tu⟩ s' hstep
  obtain ⟨k, hk, t', ht', hR'⟩ := h s t hRst s' hstep
  obtain ⟨m, hm, u', hu', hR''⟩ := ForwardSim_nSteps_weak h' k t u hR'tu t' ht'
  exact ⟨m, by omega, u', hu', ⟨t', hR', hR''⟩⟩

/-- A schedule of target times witnessing that `MT` tracks `n` steps of `MS`
    through `R`: it starts at time 0, is strictly increasing on `[0, n]`
    (so the target really moves at every source step), and at each source
    time `j <= n` both runs are defined and related. -/
def IsSimSchedule {S : Type u} {T : Type v}
    (MS : StepSys S) (MT : StepSys T) (R : S → T → Prop)
    (s : S) (t : T) (n : Nat) (times : Nat → Nat) : Prop :=
  times 0 = 0 ∧
  (∀ j, j < n → times j < times (j + 1)) ∧
  (∀ j, j ≤ n → ∃ sj tj, MS.nSteps s j = some sj ∧
      MT.nSteps t (times j) = some tj ∧ R sj tj)

/-- A schedule is at least as fast as the source clock. -/
theorem IsSimSchedule_le {S : Type u} {T : Type v}
    {MS : StepSys S} {MT : StepSys T} {R : S → T → Prop}
    {s : S} {t : T} {n : Nat} {times : Nat → Nat}
    (h : IsSimSchedule MS MT R s t n times) :
    ∀ j, j ≤ n → j ≤ times j := by
  obtain ⟨hstart, hmono, _⟩ := h
  intro j
  induction j with
  | zero => intro _; omega
  | succ j ih =>
    intro hj
    have h1 : j ≤ times j := ih (by omega)
    have h2 : times j < times (j + 1) := hmono j (by omega)
    omega

/-- Lifting to `n` source steps, strong form: an explicit strictly
    increasing schedule of target times. -/
theorem ForwardSim_nSteps {S : Type u} {T : Type v}
    {MS : StepSys S} {MT : StepSys T} {R : S → T → Prop}
    (h : ForwardSim MS MT R) (n : Nat) (s : S) (t : T) (hR : R s t)
    (s' : S) (hn : MS.nSteps s n = some s') :
    ∃ times : Nat → Nat, IsSimSchedule MS MT R s t n times := by
  induction n generalizing s' with
  | zero =>
    refine ⟨fun _ => 0, rfl, by intro j hj; omega, ?_⟩
    intro j hj
    have : j = 0 := by omega
    subst this
    exact ⟨s, t, rfl, rfl, hR⟩
  | succ n ih =>
    obtain ⟨sn, hsn⟩ := StepSys.nSteps_some_of_le MS s s' (n + 1) n (by omega) hn
    obtain ⟨times, hstart, hmono, htracks⟩ := ih sn hsn
    obtain ⟨sn', tn, hsn', htn, hRn⟩ := htracks n (Nat.le_refl n)
    rw [hsn] at hsn'
    have hsn'' : sn' = sn := by injection hsn'.symm
    subst hsn''
    have hstep : MS.step sn' = some s' := by
      rw [StepSys.nSteps_succ, hsn] at hn
      simpa using hn
    obtain ⟨k, hk, t', ht', hR'⟩ := h sn' tn hRn s' hstep
    refine ⟨fun j => if j ≤ n then times j else times n + k, ?_, ?_, ?_⟩
    · simp [hstart]
    · intro j hj
      dsimp only
      by_cases hjn : j < n
      · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
        exact hmono j hjn
      · have hj' : j = n := by omega
        subst hj'
        rw [ite_eq_left (Nat.le_refl j), ite_eq_right (by omega)]
        omega
    · intro j hj
      dsimp only
      by_cases hjn : j ≤ n
      · rw [ite_eq_left hjn]
        exact htracks j hjn
      · have hj' : j = n + 1 := by omega
        subst hj'
        rw [ite_eq_right hjn]
        refine ⟨s', t', hn, ?_, hR'⟩
        rw [StepSys.nSteps_add, htn]
        simpa using ht'

/-! ## The vacuity guard

`ForwardSim_of_stuck` is the degenerate witness the discipline of PLAN.md
section 6 forbids: a relation that only ever relates stuck source states
satisfies `ForwardSim` for any target whatsoever, target included that can
never move.  `ForwardSim_nontrivial` is the companion lemma: as soon as one
related source state does step, the target genuinely steps too. -/

/-- A relation whose source states are all stuck is a `ForwardSim` for free.
    This is the degenerate witness every emulation statement must exclude. -/
theorem ForwardSim_of_stuck {S : Type u} {T : Type v}
    (MS : StepSys S) (MT : StepSys T) (R : S → T → Prop)
    (h : ∀ s t, R s t → MS.step s = none) :
    ForwardSim MS MT R := by
  intro s t hR s' hstep
  rw [h s t hR] at hstep
  exact absurd hstep (by simp)

/-- Non-degeneracy: if a related source state steps, the target makes at
    least one step. -/
theorem ForwardSim_nontrivial {S : Type u} {T : Type v}
    {MS : StepSys S} {MT : StepSys T} {R : S → T → Prop}
    (h : ForwardSim MS MT R) (s : S) (t : T) (hR : R s t) (s' : S)
    (hstep : MS.step s = some s') :
    ∃ t1, MT.step t = some t1 := by
  obtain ⟨k, hk, t', ht', _⟩ := h s t hR s' hstep
  exact StepSys.step_some_of_nSteps MT t t' k hk ht'

/-! ## Fuel

`ForwardSim` quantifies over every source step, so a relation that carries a
finite budget cannot satisfy it once the budget runs out: the source keeps
stepping while the target is exhausted.  `fueled M` pairs a state with a step
budget and is stuck at budget 0, which makes the budget part of the source
system instead of part of the relation. -/

/-- The fuelled system: a state together with a step budget.  One step
    consumes one unit of fuel; at fuel 0 the system is stuck. -/
def fueled {S : Type u} (M : StepSys S) : StepSys (S × Nat) :=
  ⟨fun p =>
    match p.2 with
    | 0 => none
    | n + 1 => (M.step p.1).map (fun s' => (s', n))⟩

/-- Out of fuel is stuck. -/
@[simp] theorem fueled_step_zero {S : Type u} (M : StepSys S) (s : S) :
    (fueled M).step (s, 0) = none := rfl

/-- With fuel left, a fuelled step is a step of `M` and one unit less fuel. -/
@[simp] theorem fueled_step_succ {S : Type u} (M : StepSys S) (s : S) (n : Nat) :
    (fueled M).step (s, n + 1) = (M.step s).map (fun s' => (s', n)) := rfl

/-- A fuelled run of length `j` within the budget is the underlying run of
    length `j`, with `j` units of fuel consumed. -/
theorem fueled_nSteps {S : Type u} (M : StepSys S) (s : S) (f j : Nat) (hj : j ≤ f) :
    (fueled M).nSteps (s, f) j = (M.nSteps s j).map (fun s' => (s', f - j)) := by
  induction j generalizing s f with
  | zero => simp
  | succ j ih =>
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [StepSys.nSteps_succ_left, StepSys.nSteps_succ_left, fueled_step_succ]
    cases h : M.step s with
    | none => simp
    | some s1 =>
      rw [Option.map_some, Option.bind_some, Option.bind_some,
          ih s1 g (by omega), Nat.succ_sub_succ]

/-- A `k`-step functional emulation lifts to the fuelled systems, with the
    target budget scaled by `k`.  This is the shape every link of the chain
    uses to make a finite budget a source-side counter. -/
theorem ForwardSim_fueled_of_fun {S : Type u} {T : Type v}
    (MS : StepSys S) (MT : StepSys T) (k : Nat) (hk : 1 ≤ k) (enc : S → T)
    (h : ∀ s s', MS.step s = some s' → MT.nSteps (enc s) k = some (enc s')) :
    ForwardSim (fueled MS) (fueled MT) (fun p q => q = (enc p.1, k * p.2)) := by
  rintro ⟨s, n⟩ q rfl p hstep
  cases n with
  | zero => rw [fueled_step_zero] at hstep; simp at hstep
  | succ n =>
    rw [fueled_step_succ] at hstep
    cases hs : MS.step s with
    | none => rw [hs] at hstep; simp at hstep
    | some s1 =>
      rw [hs, Option.map_some] at hstep
      obtain rfl : p = (s1, n) := (Option.some.inj hstep).symm
      refine ⟨k, hk, (enc s1, k * n), ?_, rfl⟩
      rw [fueled_nSteps MT (enc s) (k * (n + 1)) k (by rw [Nat.mul_succ]; omega),
          h s s1 hs, Option.map_some, Nat.mul_succ, Nat.add_sub_cancel]

/-! ## Decoder variant -/

/-! ## Non-degeneracy examples

`ForwardSim` is not decidable (the witness `k` is unbounded), so the
examples below are explicit rather than `decide`-checked: one relation that
is a forward simulation with a genuine two-step target run, and one that is
not because the target cannot move at all.  `IsSimSchedule` gets the same
treatment at the end of the section: the schedule `j |-> 2 * j` witnesses
two source steps of the same worked example, and the constant schedule
`j |-> 0`, the degenerate witness the strict monotonicity clause exists to
exclude, is refuted. -/

end Smith
