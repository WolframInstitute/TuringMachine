/-
  Smith.Guards

  PLAN.md target T6, link H, first part (milestone M7): the guarded System 4
  tape. Smith's finite initial condition turns the head round at the left
  end of the System 4 tape with the string `0^m 2 2 1^t` (TM23Proof.pdf
  p. 44: "a lot of 0s and 221"), which cannot be chained after another
  initial condition (p. 25-26). The concatenable left end of p. 12-13 is, in
  System 4 terms, a row of guard sets `{2^w - 1}` separated by stars in front
  of the tape: a return of the head to the left end walks over the sets
  merged so far, deletes the next star (state B) and scans the merged sets,
  none of which contains 0 while stars remain, so the head arrives back on
  the leftmost element of the original tape in state B, exactly as the turn
  of the unguarded tape would have left it. This module proves that padded
  simulation: every step of a well-formed System 4 tape is matched by one
  step of the padded tape, or by `2t + 4` steps for the turn after `t` turns.

  Contents: `gset`, `guardPairs`, `merged`, `padCfg`, `RepPad`,
  `pad_turn`, `pad_forwardSim`.
-/

import Smith.Conjecture4

namespace Smith

open TM
open BiTM

/-- The set `{n - k}`. -/
def gset (n k : Nat) : List Int := [(n : Int) - k]

/-- `k` guards, each the set `{n - 1}` followed by a star, left to right. -/
def guardPairs (n : Nat) : Nat → List System4Elem
  | 0 => []
  | k + 1 => System4Elem.set (gset n 1) :: System4Elem.star :: guardPairs n k

theorem guardPairs_succ' (n k : Nat) :
    guardPairs n (k + 1) = guardPairs n k ++ [System4Elem.set (gset n 1), System4Elem.star] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show System4Elem.set (gset n 1) :: System4Elem.star :: guardPairs n (k + 1)
      = (System4Elem.set (gset n 1) :: System4Elem.star :: guardPairs n k) ++ _
    rw [ih]
    rfl

@[simp] theorem length_guardPairs (n k : Nat) : (guardPairs n k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [guardPairs, ih]; omega

/-- The sets right of the last remaining star after `t` turns: the guards
    `{n-1}, ..., {n-t}` whose stars were deleted, each scanned once per turn
    since, and the innermost `{n-2-t}`. -/
def merged (n t : Nat) : List (List Int) :=
  (List.range t).map (fun i => gset n (1 + i)) ++ [gset n (2 + t)]

theorem length_merged (n t : Nat) : (merged n t).length = t + 1 := by simp [merged]

theorem merged_ne_nil (n t : Nat) : merged n t ≠ [] := by simp [merged]

theorem decr_gset (n k : Nat) (hk : k < n) : decr (gset n k) = gset n (k + 1) := by
  unfold decr decrementSet gset
  rw [if_neg (by simp; omega)]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  push_cast
  omega

theorem merged_map_decr (n t : Nat) (ht : t + 3 ≤ n) :
    (merged n t).map decr = (List.range t).map (fun i => gset n (2 + i)) ++ [gset n (3 + t)] := by
  simp only [merged, List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [decr_gset n (1 + i) (by omega)]
    congr 1
    omega
  · rw [decr_gset n (2 + t) (by omega), show 2 + t + 1 = 3 + t from by omega]

theorem merged_succ (n t : Nat) (ht : t + 3 ≤ n) :
    merged n (t + 1) = gset n 1 :: (merged n t).map decr := by
  rw [merged_map_decr n t ht]
  unfold merged
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append]
  congr 1
  congr 1
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    congr 1
    omega
  · rw [show 2 + (t + 1) = 3 + t from by omega]

theorem parMem_false_of_forall (x : Int) (K : List (List Int)) (h : ∀ S ∈ K, x ∉ S) :
    parMem x K = false := by
  induction K with
  | nil => rfl
  | cons S K ih =>
    rw [parMem_cons, ih (fun S' hS' => h S' (List.mem_cons_of_mem _ hS')),
      decide_eq_false (h S List.mem_cons_self)]
    rfl

theorem mem_merged (n t : Nat) (S : List Int) (hS : S ∈ merged n t) :
    ∃ k, 1 ≤ k ∧ k ≤ t + 2 ∧ S = gset n k := by
  simp only [merged, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hS
  rcases hS with ⟨i, hi, rfl⟩ | rfl
  · exact ⟨1 + i, by omega, by omega, rfl⟩
  · exact ⟨2 + t, by omega, by omega, rfl⟩

theorem parMem_zero_merged (n t : Nat) (ht : t + 3 ≤ n) : parMem 0 (merged n t) = false := by
  apply parMem_false_of_forall
  intro S hS
  obtain ⟨k, hk1, hk2, rfl⟩ := mem_merged n t S hS
  simp [gset]
  omega

/-! ## The padded configuration -/

/-- The padded configuration after `t` turns: the remaining guard pairs, the
    merged sets, and the original tape. -/
def padCfg (n r t : Nat) (c : System4Config) : System4Config :=
  ⟨guardPairs n (r - 1 - t) ++ sets (merged n t) ++ c.elems,
   2 * (r - 1 - t) + (t + 1) + c.active, c.state⟩

/-- The relation of the padded simulation with `h` System 4 steps left. -/
def RepPad (n r h : Nat) (c' c : System4Config) : Prop :=
  c.WellFormed ∧ ∃ t, t + h + 1 ≤ r ∧ t + h + 3 ≤ n ∧ c' = padCfg n r t c

/-- A focus for a configuration whose head is on the tape. -/
theorem focus_of_lt (c : System4Config) (h : c.active < c.elems.length) :
    ∃ L e R, c = ⟨L ++ e :: R, L.length, c.state⟩ := by
  obtain ⟨elems, act, st⟩ := c
  simp only at h
  refine ⟨elems.take act, elems[act], elems.drop (act + 1), ?_⟩
  simp only [System4Config.mk.injEq, List.length_take, Nat.min_eq_left (le_of_lt h), and_true, true_and]
  rw [← List.drop_eq_getElem_cons h, List.take_append_drop]

theorem step_active_lt (c c1 : System4Config) (hs : System4.step c = some c1) :
    c.active < c.elems.length := by
  by_contra hlt
  unfold System4.step at hs
  rw [dif_neg hlt] at hs
  cases hs

/-- The turn on the padded tape: `2t + 4` steps. -/
theorem pad_turn (n r t : Nat) (s : List Int) (R : List System4Elem) (hr : t + 2 ≤ r) (hn : t + 3 ≤ n) :
    System4.nSteps (padCfg n r t ⟨System4Elem.set s :: R, 0, System4State.A⟩) (2 * t + 4)
      = some (padCfg n r (t + 1) ⟨System4Elem.set s :: R, 0, System4State.B⟩) := by
  obtain ⟨k, hk⟩ : ∃ k, r - 1 - t = k + 1 := ⟨r - 2 - t, by omega⟩
  have hk' : r - 1 - (t + 1) = k := by omega
  obtain ⟨K0, K', hK⟩ := List.exists_cons_of_ne_nil (merged_ne_nil n t)
  have hKlen : K'.length = t := by
    have := length_merged n t
    rw [hK] at this
    simp at this
    omega
  -- the padded configuration in focus form
  have e0 : padCfg n r t ⟨System4Elem.set s :: R, 0, System4State.A⟩
      = ⟨((guardPairs n k ++ [System4Elem.set (gset n 1), System4Elem.star]) ++ sets (merged n t))
          ++ System4Elem.set s :: R,
         ((guardPairs n k ++ [System4Elem.set (gset n 1), System4Elem.star]) ++ sets (merged n t)).length,
         System4State.A⟩ := by
    simp only [padCfg, hk, guardPairs_succ', System4Config.mk.injEq, List.append_assoc, true_and,
      and_true]
    simp [sets, length_merged] <;> omega
  rw [e0, show 2 * t + 4 = 1 + (t + (1 + (1 + (t + 1)))) from by omega, System4.nSteps_add,
    System4.nSteps_one, step_setA _ _ _ (by simp), Option.bind_some]
  -- the walk over the merged sets
  have e1 : ((guardPairs n k ++ [System4Elem.set (gset n 1), System4Elem.star]) ++ sets (merged n t)).length - 1
      = (guardPairs n k ++ [System4Elem.set (gset n 1), System4Elem.star]).length + t := by
    simp [sets, length_merged]; omega
  rw [e1, System4.nSteps_add,
    moveLeft _ (merged n t) _ t (by rw [length_merged]; omega), Option.bind_some, System4.nSteps_add,
    System4.nSteps_one]
  -- onto the star
  have e2 : (guardPairs n k ++ [System4Elem.set (gset n 1), System4Elem.star]) ++ sets (merged n t)
        ++ System4Elem.set s :: R
      = (guardPairs n k ++ [System4Elem.set (gset n 1), System4Elem.star]) ++ System4Elem.set K0 ::
          (sets K' ++ System4Elem.set s :: R) := by
    rw [hK, sets_cons]; simp
  rw [e2, step_setA _ _ _ (by simp), Option.bind_some]
  -- the star is deleted
  have e3 : (guardPairs n k ++ [System4Elem.set (gset n 1), System4Elem.star]) ++ System4Elem.set K0 ::
        (sets K' ++ System4Elem.set s :: R)
      = (guardPairs n k ++ [System4Elem.set (gset n 1)]) ++ System4Elem.star ::
          (sets (merged n t) ++ System4Elem.set s :: R) := by
    rw [hK, sets_cons]; simp
  have e4 : (guardPairs n k ++ [System4Elem.set (gset n 1), System4Elem.star]).length - 1
      = (guardPairs n k ++ [System4Elem.set (gset n 1)]).length := by simp
  rw [e3, e4, System4.nSteps_add, System4.nSteps_one, step_starA, Option.bind_some]
  -- the sweep of the merged sets
  have hsw := sweep (guardPairs n k ++ [System4Elem.set (gset n 1)]) (merged n t)
    (System4Elem.set s :: R) System4State.B (by decide)
  rw [length_merged, parMem_zero_merged n t hn] at hsw
  rw [← List.append_assoc, hsw]
  simp only [padCfg, hk', merged_succ n t hn, sets_cons, flip, Bool.false_eq_true, if_false,
    System4Config.mk.injEq, List.append_assoc, List.cons_append, List.singleton_append,
    List.length_append, length_guardPairs, List.length_singleton, length_merged, true_and, and_true]
  simp [sets, List.length_map] <;> omega

/-- The padded simulation: System 4 with guards tracks System 4. -/
theorem pad_forwardSim (n r : Nat) :
    ForwardSim (fueled system4Sys) system4Sys (fun p c' => RepPad n r p.2 c' p.1) := by
  rintro ⟨⟨elems, act, st⟩, h⟩ c' ⟨hwf, t, hr, hn, rfl⟩ p hstep
  simp only at hwf hr hn
  cases h with
  | zero => rw [fueled_step_zero] at hstep; exact absurd hstep (by simp)
  | succ h =>
    rw [fueled_step_succ] at hstep
    cases hs : system4Sys.step ⟨elems, act, st⟩ with
    | none => rw [hs] at hstep; exact absurd hstep (by simp)
    | some c1 =>
      rw [hs, Option.map_some] at hstep
      obtain rfl : p = (c1, h) := (Option.some.inj hstep).symm
      rw [system4Sys_step] at hs
      have hwf1 := System4_step_wellFormed _ c1 hwf hs
      obtain ⟨L, e, R, hc⟩ := focus_of_lt ⟨elems, act, st⟩ (step_active_lt _ c1 hs)
      simp only [System4Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, -⟩ := hc
      -- the padded configuration in focus form, for every rule but the turn
      have hpad : ∀ (L' : List System4Elem) (act' : Nat) (st' : System4State),
          padCfg n r t ⟨L', act', st'⟩ = ⟨(guardPairs n (r - 1 - t) ++ sets (merged n t)) ++ L',
            (guardPairs n (r - 1 - t) ++ sets (merged n t)).length + act', st'⟩ := by
        intro L' act' st'
        simp only [padCfg, List.length_append, length_guardPairs, sets, List.length_map,
          length_merged, List.append_assoc]
      have hGlen : (guardPairs n (r - 1 - t) ++ sets (merged n t)).length + L.length
          = ((guardPairs n (r - 1 - t) ++ sets (merged n t)) ++ L).length := by
        simp; omega
      cases e with
      | set s =>
        cases st with
        | A =>
          cases L with
          | nil =>
            simp only [List.nil_append, List.length_nil] at hs hwf1 ⊢
            rw [step_setA_zero] at hs
            obtain rfl := Option.some.inj hs
            refine ⟨2 * t + 4, by omega, _,
              by rw [system4Sys_nSteps]; exact pad_turn n r t s R (by omega) (by omega),
              hwf1, t + 1, by omega, by omega, rfl⟩
          | cons e0 L' =>
            rw [step_setA _ _ _ (by simp)] at hs
            obtain rfl := Option.some.inj hs
            refine ⟨1, le_refl 1, _, ?_, hwf1, t, by omega, by omega, rfl⟩
            rw [system4Sys_nSteps, System4.nSteps_one, hpad, hpad, ← List.append_assoc, hGlen,
              step_setA _ _ _ (by simp)]
            simp <;> omega
        | B =>
          rw [step_setB] at hs
          obtain rfl := Option.some.inj hs
          refine ⟨1, le_refl 1, _, ?_, hwf1, t, by omega, by omega, rfl⟩
          rw [system4Sys_nSteps, System4.nSteps_one, hpad, hpad, ← List.append_assoc, hGlen, step_setB]
          simp <;> omega
        | C =>
          rw [step_setC] at hs
          obtain rfl := Option.some.inj hs
          refine ⟨1, le_refl 1, _, ?_, hwf1, t, by omega, by omega, rfl⟩
          rw [system4Sys_nSteps, System4.nSteps_one, hpad, hpad, ← List.append_assoc, hGlen, step_setC]
          simp <;> omega
      | star =>
        cases st with
        | A =>
          rw [step_starA] at hs
          obtain rfl := Option.some.inj hs
          refine ⟨1, le_refl 1, _, ?_, hwf1, t, by omega, by omega, rfl⟩
          rw [system4Sys_nSteps, System4.nSteps_one, hpad, hpad, ← List.append_assoc, hGlen, step_starA]
          simp <;> omega
        | B =>
          cases L with
          | nil =>
            exfalso
            simp [System4.step] at hs
          | cons e0 L' =>
            rw [step_starB _ _ (by simp)] at hs
            obtain rfl := Option.some.inj hs
            refine ⟨1, le_refl 1, _, ?_, hwf1, t, by omega, by omega, rfl⟩
            rw [system4Sys_nSteps, System4.nSteps_one, hpad, hpad, ← List.append_assoc, hGlen,
              step_starB _ _ (by simp)]
            simp <;> omega
        | C =>
          cases R with
          | nil =>
            exfalso
            simp [System4.step] at hs
          | cons e1 R' =>
            cases e1 with
            | star =>
              exfalso
              simp [System4.step] at hs
            | set s =>
              rw [step_starC] at hs
              obtain rfl := Option.some.inj hs
              refine ⟨1, le_refl 1, _, ?_, hwf1, t, by omega, by omega, rfl⟩
              rw [system4Sys_nSteps, System4.nSteps_one, hpad, hpad, ← List.append_assoc, hGlen,
                step_starC]
              simp <;> omega

end Smith
