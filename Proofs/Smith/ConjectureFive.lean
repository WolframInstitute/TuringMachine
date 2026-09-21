/-
  Smith.ConjectureFive

  PLAN.md target T1, the finite form of Smith's Conjecture 5 (milestone M2,
  TM23Proof.pdf p. 19-20): the System 5 program `cy2s5.pl` emits for a
  cyclic tag system `C0`, a working string and a budget `N` emulates `C0`
  for as many steps as the budget affords, in the sense of `Represents`.

  The per-step lemma of `Smith.Conjecture5` is assembled here into the
  emulation calculus of `Smith.Simulation`.  The budget is carried by the
  source system: `fueled (ctsSys C0)` pairs a cyclic tag configuration with
  a step budget and is stuck at budget 0, which is what lets a relation with
  a finite budget satisfy `ForwardSim` (a fixed budget cannot, since the
  cyclic tag system steps on after the System 5 program has run out of
  rules).

  Contents:
    * `ForwardSim_congr`: transport of a forward simulation along a
      pointwise equivalence of relations, used to read the composite
      relation of `ForwardSim_comp` in its unpacked form.
    * `represents_forwardSim`: `Represents` is a forward simulation from the
      fuelled DOUBLED cyclic tag system into System 5.  One unit of fuel is
      one appendant of budget.
    * `cts_system5_forwardSim`: composed with `double_forwardSim_fueled`
      (one original step = two doubled steps, so the budget doubles), the
      same for the original cyclic tag system.
    * `conjecture5_isSimSchedule`, `conjecture5_finite`: T1 itself, an
      explicit strictly increasing schedule of System 5 times at which the
      run of `ctsToSystem5 C0 cfg N` represents the cyclic tag run.
    * `conjecture5_decode`: the decoded form, `decodeBag` of the System 5
      bag is the doubled working string at every scheduled time.
    * `idSys`, `sim_schedule_le`, `conjecture5_times_ge`: the schedule is at
      least as fast as the source clock, so it is not a degenerate witness.
    * `decide`-checked instances: the p. 29 program at the scheduled times
      0, 4, 10 and `test1.cy` at 0, 6, 12, 16, 22, 28, 40, 44, 50, both
      against `dbl` of the cyclic tag working strings, with negative
      instances at unscheduled times.
-/

import Smith.Conjecture5

namespace Smith

open TagSystem
open BiTM

universe u v

/-! ## Transport of a forward simulation -/

/-- A forward simulation transports along a pointwise equivalence of
    relations.  `ForwardSim_comp` produces the relation `Rcomp`, which is an
    existential over the intermediate state; for a functional intermediate
    encoder that existential is redundant and this lemma removes it. -/
theorem ForwardSim_congr {S : Type u} {T : Type v}
    {MS : StepSys S} {MT : StepSys T} {R R' : S → T → Prop}
    (h : ForwardSim MS MT R) (hiff : ∀ s t, R' s t ↔ R s t) :
    ForwardSim MS MT R' := by
  intro s t hR s' hstep
  obtain ⟨k, hk, t', ht', hR'⟩ := h s t ((hiff s t).mp hR) s' hstep
  exact ⟨k, hk, t', ht', (hiff s' t').mpr hR'⟩

/-! ## Link B as a forward simulation -/

/-- T1 as a `ForwardSim`: a System 5 configuration that represents a
    doubled cyclic tag configuration with budget `n + 1` runs, in at least
    one step, into one that represents the next cyclic tag configuration
    with budget `n`.  The budget is the fuel of the source system, so a
    source step at fuel `n + 1` lands at fuel `n`.

    This is `represents_step_double` of `Smith.Conjecture5` packaged in the
    calculus of `Smith.Simulation`. -/
theorem represents_forwardSim (C0 : CTS) :
    ForwardSim (fueled (ctsSys (double C0))) system5Sys
      (fun p s => Represents s (double C0) p.1 p.2) := by
  rintro ⟨⟨data, ph⟩, f⟩ s hR p hstep
  cases f with
  | zero => rw [fueled_step_zero] at hstep; exact absurd hstep (by simp)
  | succ n =>
    rw [fueled_step_succ] at hstep
    cases hc : (ctsSys (double C0)).step { data := data, phase := ph } with
    | none => rw [hc] at hstep; exact absurd hstep (by simp)
    | some c1 =>
      rw [hc, Option.map_some] at hstep
      obtain rfl : p = (c1, n) := (Option.some.inj hstep).symm
      have hne : data ≠ [] := by
        rintro rfl
        rw [ctsSys_step, CTS_step_nil] at hc
        exact absurd hc (by simp)
      obtain ⟨k, hk, s', hrun, c2, hstep2, hrep, -⟩ :=
        represents_step_double C0 { data := data, phase := ph } n s hne hR
      rw [ctsSys_step] at hc
      obtain rfl : c2 = c1 := Option.some.inj (hstep2.symm.trans hc)
      exact ⟨k, hk, s', by rw [system5Sys_nSteps]; exact hrun, hrep⟩

/-- T1 for the original, undoubled cyclic tag system: `Represents` composed
    with the doubling of `Smith.Doubling`.  One original step is two doubled
    steps, so one unit of original fuel is two appendants of budget. -/
theorem cts_system5_forwardSim (C0 : CTS) :
    ForwardSim (fueled (ctsSys C0)) system5Sys
      (fun p s => Represents s (double C0) (dblCfg p.1) (2 * p.2)) := by
  refine ForwardSim_congr
    (ForwardSim_comp (double_forwardSim_fueled C0) (represents_forwardSim C0))
    (fun p s => ⟨fun hrep => ⟨(dblCfg p.1, 2 * p.2), rfl, hrep⟩, ?_⟩)
  rintro ⟨q, rfl, hrep⟩
  exact hrep

/-! ## T1, the finite form of Conjecture 5 -/

/-- T1 in the `IsSimSchedule` form of `Smith.Simulation`: for a cyclic tag
    run of `n` steps within the budget there is a strictly increasing
    schedule of System 5 times at which the run of the encoder output is
    related to it. -/
theorem conjecture5_isSimSchedule (C0 : CTS) (cfg : CTSConfig) (N n : Nat)
    (hn : n ≤ C0.appendants.length * N) (c' : CTSConfig)
    (hrun : C0.nSteps cfg n = some c') :
    ∃ times : Nat → Nat,
      IsSimSchedule (fueled (ctsSys C0)) system5Sys
        (fun p s => Represents s (double C0) (dblCfg p.1) (2 * p.2))
        (cfg, C0.appendants.length * N) (ctsToSystem5 C0 cfg N) n times := by
  refine ForwardSim_nSteps (cts_system5_forwardSim C0) n
    (cfg, C0.appendants.length * N) (ctsToSystem5 C0 cfg N)
    (ctsToSystem5_represents C0 cfg N) (c', C0.appendants.length * N - n) ?_
  rw [fueled_nSteps _ _ _ _ hn, ctsSys_nSteps, hrun]
  rfl

/-- T1, the finite form of Conjecture 5 (PLAN.md section 2).  For every
    cyclic tag system `C0`, initial configuration `cfg` and budget `N`, the
    System 5 program `ctsToSystem5 C0 cfg N` emulates `C0` for every number
    of steps `n` the budget affords: there are strictly increasing times
    `times 0 = 0 < times 1 < ... < times n` such that after `times j` System
    5 steps the configuration represents the `j`-th cyclic tag
    configuration of the DOUBLED system, with `j` appendant pairs of budget
    consumed.

    `Represents` is Smith's p. 19 "acceptable initial condition" relation
    (in the canonical `cy2s5.pl` spacing, see the fidelity note of
    `Smith.Represents`), not equality with the encoder output. -/
theorem conjecture5_finite (C0 : CTS) (cfg : CTSConfig) (N n : Nat)
    (hn : n ≤ C0.appendants.length * N) (c' : CTSConfig)
    (hrun : C0.nSteps cfg n = some c') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ j, j < n → times j < times (j + 1)) ∧
      ∀ j, j ≤ n → ∃ cj sj, C0.nSteps cfg j = some cj ∧
        System5.nSteps (ctsToSystem5 C0 cfg N) (times j) = some sj ∧
        Represents sj (double C0) (dblCfg cj)
          (2 * (C0.appendants.length * N - j)) := by
  obtain ⟨times, h0, hmono, htrack⟩ := conjecture5_isSimSchedule C0 cfg N n hn c' hrun
  refine ⟨times, h0, hmono, ?_⟩
  intro j hj
  obtain ⟨pj, sj, hsrc, htgt, hrel⟩ := htrack j hj
  rw [fueled_nSteps _ _ _ _ (Nat.le_trans hj hn), ctsSys_nSteps] at hsrc
  cases hcj : C0.nSteps cfg j with
  | none => rw [hcj] at hsrc; exact absurd hsrc (by simp)
  | some cj =>
    rw [hcj, Option.map_some] at hsrc
    obtain rfl : pj = (cj, C0.appendants.length * N - j) := (Option.some.inj hsrc).symm
    exact ⟨cj, sj, rfl, by rw [← system5Sys_nSteps]; exact htgt, hrel⟩

/-! ## T1 with the rule count

`Represents` leaves the rules beyond the budget unconstrained.  The per-step
lemmas pop exactly two rules per appendant, so on the encoder output, whose
rule list has two rules per appendant of budget, the rule list is always
exactly twice the budget long; at the end of the budget it is empty, which is
the terminal event of the System 4 emulation (T2's exit in state C). -/

/-- `Represents` with the rule list exactly two rules per appendant of
    budget long. -/
def RepresentsExact (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat) : Prop :=
  Represents s C c b ∧ s.rules.length = 2 * b

theorem represents_exact_forwardSim (C0 : CTS) :
    ForwardSim (fueled (ctsSys (double C0))) system5Sys
      (fun p s => RepresentsExact s (double C0) p.1 p.2) := by
  rintro ⟨⟨data, ph⟩, f⟩ s ⟨hR, hlen⟩ p hstep
  cases f with
  | zero => rw [fueled_step_zero] at hstep; exact absurd hstep (by simp)
  | succ n =>
    rw [fueled_step_succ] at hstep
    cases hc : (ctsSys (double C0)).step { data := data, phase := ph } with
    | none => rw [hc] at hstep; exact absurd hstep (by simp)
    | some c1 =>
      rw [hc, Option.map_some] at hstep
      obtain rfl : p = (c1, n) := (Option.some.inj hstep).symm
      have hne : data ≠ [] := by
        rintro rfl
        rw [ctsSys_step, CTS_step_nil] at hc
        exact absurd hc (by simp)
      obtain ⟨k, hk, s', hrun, c2, hstep2, hrep, hlen'⟩ :=
        represents_step_double C0 { data := data, phase := ph } n s hne hR
      rw [ctsSys_step] at hc
      obtain rfl : c2 = c1 := Option.some.inj (hstep2.symm.trans hc)
      exact ⟨k, hk, s', by rw [system5Sys_nSteps]; exact hrun, hrep, by omega⟩

theorem cts_system5_exact_forwardSim (C0 : CTS) :
    ForwardSim (fueled (ctsSys C0)) system5Sys
      (fun p s => RepresentsExact s (double C0) (dblCfg p.1) (2 * p.2)) := by
  refine ForwardSim_congr
    (ForwardSim_comp (double_forwardSim_fueled C0) (represents_exact_forwardSim C0))
    (fun p s => ⟨fun hrep => ⟨(dblCfg p.1, 2 * p.2), rfl, hrep⟩, ?_⟩)
  rintro ⟨q, rfl, hrep⟩
  exact hrep

theorem ctsToSystem5_representsExact (C : CTS) (cfg : CTSConfig) (N : Nat) :
    RepresentsExact (ctsToSystem5 C cfg N) (double C) (dblCfg cfg)
      (2 * (C.appendants.length * N)) := by
  refine ⟨ctsToSystem5_represents C cfg N, ?_⟩
  rw [ctsToSystem5_rules_eq, ctsRulesToSystem5Rules_length, Nat.mul_assoc]
  omega

/-- T1 with the rule count: the schedule of `conjecture5_finite`, and at
    every scheduled time the rule list is exactly twice the remaining
    budget long; at the end of the budget it is empty. -/
theorem conjecture5_finite_exact (C0 : CTS) (cfg : CTSConfig) (N n : Nat)
    (hn : n ≤ C0.appendants.length * N) (c' : CTSConfig)
    (hrun : C0.nSteps cfg n = some c') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ j, j < n → times j < times (j + 1)) ∧
      ∀ j, j ≤ n → ∃ cj sj, C0.nSteps cfg j = some cj ∧
        System5.nSteps (ctsToSystem5 C0 cfg N) (times j) = some sj ∧
        Represents sj (double C0) (dblCfg cj) (2 * (C0.appendants.length * N - j)) ∧
        sj.rules.length = 2 * (2 * (C0.appendants.length * N - j)) := by
  obtain ⟨times, h0, hmono, htrack⟩ := ForwardSim_nSteps (cts_system5_exact_forwardSim C0) n
    (cfg, C0.appendants.length * N) (ctsToSystem5 C0 cfg N)
    (ctsToSystem5_representsExact C0 cfg N) (c', C0.appendants.length * N - n)
    (by rw [fueled_nSteps _ _ _ _ hn, ctsSys_nSteps, hrun]; rfl)
  refine ⟨times, h0, hmono, ?_⟩
  intro j hj
  obtain ⟨pj, sj, hsrc, htgt, hrel, hlen⟩ := htrack j hj
  rw [fueled_nSteps _ _ _ _ (Nat.le_trans hj hn), ctsSys_nSteps] at hsrc
  cases hcj : C0.nSteps cfg j with
  | none => rw [hcj] at hsrc; exact absurd hsrc (by simp)
  | some cj =>
    rw [hcj, Option.map_some] at hsrc
    obtain rfl : pj = (cj, C0.appendants.length * N - j) := (Option.some.inj hsrc).symm
    exact ⟨cj, sj, rfl, by rw [← system5Sys_nSteps]; exact htgt, hrel, hlen⟩

/-- The decoded form of T1: at every scheduled time the System 5 bag
    decodes, through `decodeBag` of `Smith.System5Runs`, to the doubled
    working string of the cyclic tag configuration at that step.  So the
    System 5 run reproduces the working strings of the cyclic tag run, with
    no existential over the pair starts left in the conclusion. -/
theorem conjecture5_decode (C0 : CTS) (cfg : CTSConfig) (N n : Nat)
    (hn : n ≤ C0.appendants.length * N) (c' : CTSConfig)
    (hrun : C0.nSteps cfg n = some c') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ j, j < n → times j < times (j + 1)) ∧
      ∀ j, j ≤ n → ∃ cj sj, C0.nSteps cfg j = some cj ∧
        System5.nSteps (ctsToSystem5 C0 cfg N) (times j) = some sj ∧
        decodeBag sj.bag = some (dbl cj.data) := by
  obtain ⟨times, h0, hmono, htrack⟩ := conjecture5_finite C0 cfg N n hn c' hrun
  refine ⟨times, h0, hmono, ?_⟩
  intro j hj
  obtain ⟨cj, sj, hcj, hsj, hrep⟩ := htrack j hj
  exact ⟨cj, sj, hcj, hsj, Represents_decode sj (double C0) (dblCfg cj) _ hrep⟩

/-! ## The schedule is not degenerate

`IsSimSchedule` forbids a constant schedule, and its `IsSimSchedule_le`
says a schedule is at least as fast as the source clock.  The same fact for
the bare clauses of `conjecture5_finite` is `sim_schedule_le`, obtained from
`IsSimSchedule_le` on the identity system, which steps forever. -/

/-- The one-state system that always steps.  Only used to read
    `IsSimSchedule_le` off the two clock clauses of a schedule. -/
def idSys : StepSys Unit := ⟨fun _ => some ()⟩

/-- The identity system runs for ever. -/
theorem idSys_nSteps (j : Nat) : idSys.nSteps () j = some () := by
  induction j with
  | zero => rfl
  | succ j ih => rw [StepSys.nSteps_succ_left]; exact ih

/-- A schedule that starts at 0 and strictly increases on `[0, n]` is at
    least as fast as the source clock.  Applied to the times of
    `conjecture5_finite` it gives `n <= times n`, so the schedule cannot be
    the degenerate constant one. -/
theorem sim_schedule_le (n : Nat) (times : Nat → Nat) (h0 : times 0 = 0)
    (hmono : ∀ j, j < n → times j < times (j + 1)) :
    ∀ j, j ≤ n → j ≤ times j :=
  IsSimSchedule_le (MS := idSys) (MT := idSys) (R := fun _ _ => True)
    (s := ()) (t := ()) (n := n) (times := times)
    ⟨h0, hmono, fun j _ => ⟨(), (), idSys_nSteps j, idSys_nSteps (times j), trivial⟩⟩

/-- T1 with the clock bound: the schedule of `conjecture5_finite` spends at
    least one System 5 step per cyclic tag step, so `n <= times n`. -/
theorem conjecture5_times_ge (C0 : CTS) (cfg : CTSConfig) (N n : Nat)
    (hn : n ≤ C0.appendants.length * N) (c' : CTSConfig)
    (hrun : C0.nSteps cfg n = some c') :
    ∃ times : Nat → Nat, (∀ j, j ≤ n → j ≤ times j) ∧ n ≤ times n ∧
      ∀ j, j ≤ n → ∃ cj sj, C0.nSteps cfg j = some cj ∧
        System5.nSteps (ctsToSystem5 C0 cfg N) (times j) = some sj ∧
        Represents sj (double C0) (dblCfg cj)
          (2 * (C0.appendants.length * N - j)) := by
  obtain ⟨times, h0, hmono, htrack⟩ := conjecture5_finite C0 cfg N n hn c' hrun
  have hle := sim_schedule_le n times h0 hmono
  exact ⟨times, hle, hle n (Nat.le_refl n), htrack⟩

/-! ## Instances

Both instances state the decoded form directly against the cyclic tag run:
`decodeBag` of the System 5 bag at the scheduled time is `dbl` of the
working string the cyclic tag system has at that step.  The times were
computed by evaluating the two runs and are stated explicitly. -/

/-- The p. 29 program `cy2s5.pl 3 01 1 10` at time 0: the encoder output
    decodes to the doubled initial working string `0011`. -/
theorem ex_c5_pdf29_time0 :
    (System5.nSteps (ctsToSystem5 exCTS exCfg 1) 0).map (fun s => decodeBag s.bag)
      = (exCTS.nSteps exCfg 0).map (fun c => some (dbl c.data)) := by decide

/-- The same program at time 4, one cyclic tag step later: the working
    string `01` has become `1`, and the bag decodes to `11`. -/
theorem ex_c5_pdf29_time4 :
    (System5.nSteps (ctsToSystem5 exCTS exCfg 1) 4).map (fun s => decodeBag s.bag)
      = (exCTS.nSteps exCfg 1).map (fun c => some (dbl c.data)) := by decide

/-- The same program at time 10, two cyclic tag steps in: the working string
    is `10` and the bag decodes to `1100`.  The budget `N = 1` is two
    cyclic tag steps, so this is the whole run T1 covers here. -/
theorem ex_c5_pdf29_time10 :
    (System5.nSteps (ctsToSystem5 exCTS exCfg 1) 10).map (fun s => decodeBag s.bag)
      = (exCTS.nSteps exCfg 2).map (fun c => some (dbl c.data)) := by decide

/-- Negative instance: at time 5, which is not a scheduled time, the bag
    does not decode at all (the block the first pop of the pair deposited
    has not been consumed yet). -/
theorem ex_c5_pdf29_time5_none :
    (System5.nSteps (ctsToSystem5 exCTS exCfg 1) 5).map (fun s => decodeBag s.bag)
      = some none := by decide

/-- Negative instance: at time 2, halfway through the first cyclic tag step,
    the bag does decode, but to the word `011`, which is the doubled system
    one step in and is not the double of any working string.  So the times
    of the schedule are not arbitrary decoding times. -/
theorem ex_c5_pdf29_time2_not_double :
    (System5.nSteps (ctsToSystem5 exCTS exCfg 1) 2).map (fun s => decodeBag s.bag)
      = some (some [false, true, true]) := by decide

/-- The word of `ex_c5_pdf29_time2_not_double` is not a doubled word: its
    length is odd. -/
theorem ex_c5_time2_word_not_dbl (w : List Bool) : dbl w ≠ [false, true, true] := by
  intro h
  have hl := dbl_length w
  rw [h] at hl
  simp at hl
  omega

/-- T1 itself on the p. 29 program, as a term: two cyclic tag steps within
    the budget `N = 1`. -/
theorem ex_c5_pdf29_conjecture5 :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ j, j < 2 → times j < times (j + 1)) ∧
      ∀ j, j ≤ 2 → ∃ cj sj, exCTS.nSteps exCfg j = some cj ∧
        System5.nSteps (ctsToSystem5 exCTS exCfg 1) (times j) = some sj ∧
        decodeBag sj.bag = some (dbl cj.data) :=
  conjecture5_decode exCTS exCfg 1 2 (by decide)
    { data := [true, false], phase := 0 } (by decide)

/-! ### `test1.cy`

The second `cy2s5.pl` vector of TM23Proof.pdf p. 28-29: working string
`11011`, appendants `101 01 0 "" 010`, budget `N = 10` (the Perl `n = 50`,
five appendants per cycle).  The scheduled times of the first eight cyclic
tag steps are 6, 12, 16, 22, 28, 40, 44 and 50; they differ because each
cyclic tag step costs `x + gap b` System 5 steps for the current smallest
bag integer `x` and leading bit `b`, twice over. -/

set_option maxRecDepth 8000 in
/-- `test1.cy` of TM23Proof.pdf p. 28. -/
def ctsTest1 : CTS where
  appendants := [[true, false, true], [false, true], [false], [],
                 [false, true, false]]
  nonempty := by decide

/-- Its working string `11011` at phase 0. -/
def cfgTest1 : CTSConfig := { data := [true, true, false, true, true], phase := 0 }

set_option maxRecDepth 8000 in
/-- `test1.cy` at time 0: the encoder output decodes to `1111001111`. -/
theorem ex_c5_test1_time0 :
    (System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) 0).map (fun s => decodeBag s.bag)
      = (ctsTest1.nSteps cfgTest1 0).map (fun c => some (dbl c.data)) := by decide

set_option maxRecDepth 8000 in
/-- `test1.cy` at time 6, one cyclic tag step in: the working string is
    `1011101`. -/
theorem ex_c5_test1_time6 :
    (System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) 6).map (fun s => decodeBag s.bag)
      = (ctsTest1.nSteps cfgTest1 1).map (fun c => some (dbl c.data)) := by decide

set_option maxRecDepth 8000 in
/-- `test1.cy` at time 12, two cyclic tag steps in: the working string is
    `01110101`. -/
theorem ex_c5_test1_time12 :
    (System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) 12).map (fun s => decodeBag s.bag)
      = (ctsTest1.nSteps cfgTest1 2).map (fun c => some (dbl c.data)) := by decide

set_option maxRecDepth 8000 in
/-- `test1.cy` at time 16, three cyclic tag steps in: the working string is
    `1110101`.  The step took 4 System 5 steps rather than 6, because the
    leading bit of the doubled string was a 0 for one of the two doubled
    steps. -/
theorem ex_c5_test1_time16 :
    (System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) 16).map (fun s => decodeBag s.bag)
      = (ctsTest1.nSteps cfgTest1 3).map (fun c => some (dbl c.data)) := by decide

set_option maxRecDepth 8000 in
/-- `test1.cy` at time 22, four cyclic tag steps in. -/
theorem ex_c5_test1_time22 :
    (System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) 22).map (fun s => decodeBag s.bag)
      = (ctsTest1.nSteps cfgTest1 4).map (fun c => some (dbl c.data)) := by decide

set_option maxRecDepth 8000 in
/-- `test1.cy` at time 28, five cyclic tag steps in. -/
theorem ex_c5_test1_time28 :
    (System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) 28).map (fun s => decodeBag s.bag)
      = (ctsTest1.nSteps cfgTest1 5).map (fun c => some (dbl c.data)) := by decide

set_option maxRecDepth 8000 in
/-- `test1.cy` at time 40, six cyclic tag steps in.  The jump of 12 System 5
    steps is one cyclic tag step over a working string whose doubled form
    starts with a 1 and whose smallest bag integer has grown. -/
theorem ex_c5_test1_time40 :
    (System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) 40).map (fun s => decodeBag s.bag)
      = (ctsTest1.nSteps cfgTest1 6).map (fun c => some (dbl c.data)) := by decide

set_option maxRecDepth 8000 in
/-- `test1.cy` at time 44, seven cyclic tag steps in. -/
theorem ex_c5_test1_time44 :
    (System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) 44).map (fun s => decodeBag s.bag)
      = (ctsTest1.nSteps cfgTest1 7).map (fun c => some (dbl c.data)) := by decide

set_option maxRecDepth 8000 in
/-- `test1.cy` at time 50, eight cyclic tag steps in.  This is the `decide`
    example on `test1.cy` for eight cyclic tag steps that PLAN.md asks of
    milestone M2. -/
theorem ex_c5_test1_time50 :
    (System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) 50).map (fun s => decodeBag s.bag)
      = (ctsTest1.nSteps cfgTest1 8).map (fun c => some (dbl c.data)) := by decide

set_option maxRecDepth 8000 in
/-- Negative instance for `test1.cy`: time 13 is not a scheduled time and
    the bag there does not decode. -/
theorem ex_c5_test1_time13_none :
    (System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) 13).map (fun s => decodeBag s.bag)
      = some none := by decide

set_option maxRecDepth 8000 in
/-- T1 on `test1.cy`, as a term: eight cyclic tag steps, well within the
    budget `5 * 10`. -/
theorem ex_c5_test1_conjecture5 :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ j, j < 8 → times j < times (j + 1)) ∧
      ∀ j, j ≤ 8 → ∃ cj sj, ctsTest1.nSteps cfgTest1 j = some cj ∧
        System5.nSteps (ctsToSystem5 ctsTest1 cfgTest1 10) (times j) = some sj ∧
        decodeBag sj.bag = some (dbl cj.data) :=
  conjecture5_decode ctsTest1 cfgTest1 10 8 (by decide)
    { data := [false, true, false, true, false, true, false, true, false], phase := 3 }
    (by decide)

end Smith
