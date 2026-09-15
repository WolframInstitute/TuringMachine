/-
  Smith.Conjecture5

  The per-step lemma of PLAN.md target T1 (milestone M2), both head cases:
  one step of a DOUBLED cyclic tag system is emulated by `x + gap b` steps
  of System 5, where `x` is the smallest bag integer and `b` the leading bit
  of the working string (TM23Proof.pdf p. 19-20).

  The run is Smith's.  In both cases the first `x - 1` steps are pure
  decrements and step `x` pops the first rule of the leading pair, which
  lands above the whole bag and is therefore appended.

  0-head (`gap = 1`, `k = x + 1`).  Step `x + 1` pops the second rule of the
  pair, which by `r1 = r2 + 2` has become exactly the block the first pop
  added and so cancels it.  What is left is the old bag minus the pair of
  the consumed bit, shifted down by `x + 1`, and the rule list is the
  remaining blocks shifted up by `x + 1`, i.e. the same canonical layout
  from the counter `i' + (x + 1)`.

  1-head (`gap = 2`, `k = x + 2`).  Step `x + 1` is a pure decrement and
  step `x + 2` pops the second rule of the pair.  The block the first pop
  appended has become `r2 + x` by then and the new one is `r2 + (x + 2)`;
  no two integers of `r2` are exactly 2 apart, so the two blocks are
  disjoint and both survive.  Together they are the canonical bag of the
  appendant laid out from `i + x`, so the new bag is the old one minus the
  consumed pair, shifted down by `x + 2`, followed by the pairs of the
  appended appendant, and the working string grows by `dbl a`, exactly as
  `CTS.step` appends it.  The threshold is met with equality: the new bag
  reaches `i' + x - 1` and the new counter is `i' + (x + 2)`.

  Contents:
    * `encodePaired_snd_pairwise`, `encodePaired_snd_nodup`: the second rule
      of a pair is strictly increasing.  `encodePaired_snd_pairwise_gap`,
      `no_gap_two_of_pairwise`, `encodePaired_snd_no_gap_two`: consecutive
      integers of a second rule are 1 or at least 3 apart, so no two of them
      are exactly 2 apart.  `encodePaired_snd_lt_counter`,
      `encodePaired_fst_lt_counter`: every rule integer of one appendant
      block lies in `[i, i' - 1]`.
    * `Represents_cons_decomp`: the decomposition of `Represents` at a
      nonempty working string, extracting the first start `x`, the remaining
      starts `a'`, the rule counters `i`, `i'`, the leading rule pair
      `r1`, `r2`, the unconstrained tail, and every inequality between them.
      Stated for an arbitrary head bit, so both cases use it.
    * `System5_run_then_pop_int`: the run of `Smith.System5Runs` indexed by
      the Int value of the elapsed time rather than by a `Nat`;
      `map_shift_comp`, two uniform increments of a rule list.
    * `System5_run_to_first_pop`: the run up to and including the pop of the
      first rule of the leading pair, stated for an arbitrary gap so that
      both cases use it.
    * `represents_step_false_time`, the 0-head per-step lemma with the step
      count pinned to `x + 1`, and `represents_step_false`, its
      `ForwardSim` shape.
    * `perm_append_shuffle`, `encodeAppendant_counter`,
      `encodeAppendant_snd_bag_perm`, `encodeAppendant_bagAux_lt`,
      `pairsOf_append`, `pairsAsc_append`, `double_currentAppendant_dbl`:
      the facts the 1-head case needs about the appendant it appends.
    * `represents_step_true_time`, the 1-head per-step lemma with the step
      count pinned to `x + 2`, and `represents_step_true`.
    * `represents_step_double_time` and `represents_step_double`: both cases
      at once, over a doubled system, with the cyclic tag step exhibited and
      the step count pinned to `x + gap b`.
    * `decide`-checked instances on the TM23Proof.pdf p. 29 program, with
      negative instances showing that no shorter run works.
-/

import Smith.System5Runs

namespace Smith

open TagSystem
open BiTM

/-! ## The second rule of a pair is strictly increasing -/

/-- The integers of the second rule of a pair are strictly increasing: the
    two integers of one doubled bit are `i, i+1` or `i, i+3`, and the next
    doubled bit starts at `i+4` or `i+6`. -/
theorem encodePaired_snd_pairwise (w : List Bool) (i : Int) :
    (encodePaired w i).2.1.Pairwise (· < ·) := by
  induction w, i using encodePaired.induct with
  | case1 b rest i r1 r2 i' heq ih =>
    show ((i : Int) :: (i + 3) :: (encodePaired rest (i + 6)).2.1).Pairwise (· < ·)
    have hge := encodePaired_snd_ge rest (i + 6)
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, ih⟩⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := hge y hy; omega
    · intro y hy
      have := hge y hy; omega
  | case2 b rest i r1 r2 i' heq ih =>
    show ((i : Int) :: (i + 1) :: (encodePaired rest (i + 4)).2.1).Pairwise (· < ·)
    have hge := encodePaired_snd_ge rest (i + 4)
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, ih⟩⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := hge y hy; omega
    · intro y hy
      have := hge y hy; omega
  | case3 t i h1 h2 =>
    cases t with
    | nil => exact List.Pairwise.nil
    | cons b t' =>
      cases t' with
      | nil => cases b <;> exact List.Pairwise.nil
      | cons b2 rest =>
        cases b with
        | true => exact (h1 b2 rest rfl).elim
        | false => exact (h2 b2 rest rfl).elim

/-- The second rule of a pair has no duplicates, which is what makes the
    cancellation of the second pop exact. -/
theorem encodePaired_snd_nodup (w : List Bool) (i : Int) :
    (encodePaired w i).2.1.Nodup := by
  refine List.Pairwise.imp ?_ (encodePaired_snd_pairwise w i)
  intro u v huv
  omega

/-- The consecutive integers of the second rule of a pair are 1 apart or at
    least 3 apart: the two integers of one doubled bit are `i, i+1` or
    `i, i+3`, and the next doubled bit starts at `i+4` or `i+6`. -/
theorem encodePaired_snd_pairwise_gap (w : List Bool) (i : Int) :
    (encodePaired w i).2.1.Pairwise (fun u v => u + 1 = v ∨ u + 3 ≤ v) := by
  induction w, i using encodePaired.induct with
  | case1 b rest i r1 r2 i' heq ih =>
    show ((i : Int) :: (i + 3) :: (encodePaired rest (i + 6)).2.1).Pairwise _
    have hge := encodePaired_snd_ge rest (i + 6)
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, ih⟩⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := hge y hy; omega
    · intro y hy
      have := hge y hy; omega
  | case2 b rest i r1 r2 i' heq ih =>
    show ((i : Int) :: (i + 1) :: (encodePaired rest (i + 4)).2.1).Pairwise _
    have hge := encodePaired_snd_ge rest (i + 4)
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, ih⟩⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := hge y hy; omega
    · intro y hy
      have := hge y hy; omega
  | case3 t i h1 h2 =>
    cases t with
    | nil => exact List.Pairwise.nil
    | cons b t' =>
      cases t' with
      | nil => cases b <;> exact List.Pairwise.nil
      | cons b2 rest =>
        cases b with
        | true => exact (h1 b2 rest rfl).elim
        | false => exact (h2 b2 rest rfl).elim

/-- A list whose consecutive integers are 1 apart or at least 3 apart holds
    no two integers exactly 2 apart. -/
theorem no_gap_two_of_pairwise (l : List Int)
    (h : l.Pairwise (fun u v => u + 1 = v ∨ u + 3 ≤ v)) :
    ∀ u ∈ l, ∀ v ∈ l, u + 2 ≠ v := by
  induction l with
  | nil => intro u hu; cases hu
  | cons c t ih =>
    rw [List.pairwise_cons] at h
    have hgt : ∀ z ∈ t, c + 1 ≤ z := by
      intro z hz
      rcases h.1 z hz with h1 | h1 <;> omega
    intro u hu v hv
    have hu' := List.mem_cons.mp hu
    have hv' := List.mem_cons.mp hv
    rcases hu' with hu1 | hu1
    · rcases hv' with hv1 | hv1
      · omega
      · rcases h.1 v hv1 with h1 | h1 <;> omega
    · have hcu := hgt u hu1
      rcases hv' with hv1 | hv1
      · omega
      · exact ih h.2 u hu1 v hv1

/-- Every integer of the second rule of a pair lies strictly below the
    counter the encoding ends at. -/
theorem encodePaired_snd_lt_counter (w : List Bool) (i : Int) :
    ∀ v ∈ (encodePaired w i).2.1, v < (encodePaired w i).2.2 := by
  induction w, i using encodePaired.induct with
  | case1 b rest i r1 r2 i' heq ih =>
    show ∀ v ∈ ((i : Int) :: (i + 3) :: (encodePaired rest (i + 6)).2.1),
      v < (encodePaired rest (i + 6)).2.2
    have hc := encodePaired_counter_ge rest (i + 6)
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · exact ih v hv
  | case2 b rest i r1 r2 i' heq ih =>
    show ∀ v ∈ ((i : Int) :: (i + 1) :: (encodePaired rest (i + 4)).2.1),
      v < (encodePaired rest (i + 4)).2.2
    have hc := encodePaired_counter_ge rest (i + 4)
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · exact ih v hv
  | case3 t i h1 h2 =>
    cases t with
    | nil => intro v hv; cases hv
    | cons b t' =>
      cases t' with
      | nil => cases b <;> (intro v hv; cases hv)
      | cons b2 rest =>
        cases b with
        | true => exact (h1 b2 rest rfl).elim
        | false => exact (h2 b2 rest rfl).elim

/-- Every integer of the first rule of a pair lies strictly below the
    counter the encoding ends at.  Together with `encodePaired_snd_ge` this
    is the containment `i <= r <= i' - 1` of every rule integer of one
    appendant block. -/
theorem encodePaired_fst_lt_counter (w : List Bool) (i : Int) :
    ∀ v ∈ (encodePaired w i).1, v < (encodePaired w i).2.2 := by
  induction w, i using encodePaired.induct with
  | case1 b rest i r1 r2 i' heq ih =>
    show ∀ v ∈ ((i + 2 : Int) :: (i + 5) :: (encodePaired rest (i + 6)).1),
      v < (encodePaired rest (i + 6)).2.2
    have hc := encodePaired_counter_ge rest (i + 6)
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · exact ih v hv
  | case2 b rest i r1 r2 i' heq ih =>
    show ∀ v ∈ ((i + 2 : Int) :: (i + 3) :: (encodePaired rest (i + 4)).1),
      v < (encodePaired rest (i + 4)).2.2
    have hc := encodePaired_counter_ge rest (i + 4)
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · exact ih v hv
  | case3 t i h1 h2 =>
    cases t with
    | nil => intro v hv; cases hv
    | cons b t' =>
      cases t' with
      | nil => cases b <;> (intro v hv; cases hv)
      | cons b2 rest =>
        cases b with
        | true => exact (h1 b2 rest rfl).elim
        | false => exact (h2 b2 rest rfl).elim

/-- No two integers of the second rule of a pair are exactly 2 apart, which
    is what keeps the two blocks of the 1-head case disjoint. -/
theorem encodePaired_snd_no_gap_two (w : List Bool) (i : Int) :
    ∀ u ∈ (encodePaired w i).2.1, ∀ v ∈ (encodePaired w i).2.1, u + 2 ≠ v :=
  no_gap_two_of_pairwise _ (encodePaired_snd_pairwise_gap w i)

/-! ## Decomposing `Represents` at a nonempty working string -/

/-- The decomposition of the representation relation at a nonempty working
    string and a nonzero budget: the first start `x`, the remaining starts
    `a'`, the rule counter `i` and the counter `i'` the leading appendant
    ends at, the leading rule pair `r1`, `r2`, the unconstrained tail
    `rest`, and every inequality the per-step lemma needs.

    Stated for an arbitrary head bit `b`, so both cases of the per-step
    lemma start from it. -/
theorem Represents_cons_decomp (C : CTS) (b : Bool) (w : List Bool) (p n : Nat)
    (s : System5Config) (h : Represents s C { data := b :: w, phase := p } (n + 1)) :
    ∃ (x : Int) (a' : List Int) (i i' : Int) (r1 r2 : List Int)
      (rest : List (List Int)),
      1 ≤ x ∧
      pairsAsc (x + gap b) w a' = true ∧
      s.bag.Perm (x :: (x + gap b) :: pairsOf w a') ∧
      (∀ y ∈ s.bag, x ≤ y) ∧
      (∀ y ∈ s.bag, y + 3 ≤ i) ∧
      encodePaired (C.currentAppendant p) i = (r1, r2, i') ∧
      r1 = r2.map (· + 2) ∧
      (∀ v ∈ r2, i ≤ v) ∧
      r2.Nodup ∧
      i ≤ i' ∧
      s.rules = r1 :: r2 :: ((ruleBlocks (appendantsFrom C (p + 1) n) i').1 ++ rest) := by
  obtain ⟨⟨a, hasc, hperm⟩, i, rest, hbound, hrules⟩ := h
  simp only [] at hasc hperm hrules
  rw [appendantsFrom_succ, ruleBlocks_cons] at hrules
  simp only [List.cons_append] at hrules
  cases a with
  | nil => simp at hasc
  | cons x a' =>
    rw [pairsAsc_cons_cons, Bool.and_eq_true, decide_eq_true_eq] at hasc
    rw [pairsOf_cons] at hperm
    refine ⟨x, a', i, (encodePaired (C.currentAppendant p) i).2.2,
            (encodePaired (C.currentAppendant p) i).1,
            (encodePaired (C.currentAppendant p) i).2.1, rest,
            by omega, hasc.2, hperm, ?_, hbound, rfl,
            encodePaired_fst_eq_snd_add_two _ _,
            encodePaired_snd_ge _ _,
            encodePaired_snd_nodup _ _,
            encodePaired_counter_ge _ _, hrules⟩
    intro y hy
    have hy' := hperm.subset hy
    rcases List.mem_cons.mp hy' with rfl | hy'
    · exact Int.le_refl _
    rcases List.mem_cons.mp hy' with rfl | hy'
    · have := gap_pos b; omega
    · have h1 := pairsOf_gt (x + gap b) w a' hasc.2 y hy'
      have h2 := gap_pos b
      omega

/-! ## The run indexed by elapsed time -/

/-- `System5_run_then_pop` with the elapsed time given as the Int value `x`
    of the bag minimum rather than as a `Nat`: `x` steps take the bag down
    by `x`, the element that was `x` reaches 0, and the head rule is popped
    shifted by `x`. -/
theorem System5_run_then_pop_int (cfg : System5Config) (x : Int) (hx : 1 ≤ x)
    (r : List Int) (rest : List (List Int)) (h_rules : cfg.rules = r :: rest)
    (h_ge : ∀ y ∈ cfg.bag, x ≤ y) (h_mem : x ∈ cfg.bag) :
    ∃ k : Nat, (k : Int) = x ∧ 1 ≤ k ∧
      System5.nSteps cfg k
        = some { bag := xorMerge ((cfg.bag.map (· - x)).erase 0) (r.map (· + x)),
                 rules := rest.map (fun t => t.map (· + x)) } := by
  obtain ⟨j, hj⟩ : ∃ j : Nat, (j : Int) + 1 = x := ⟨(x - 1).toNat, by omega⟩
  have hcast : ((j + 1 : Nat) : Int) = x := by push_cast; omega
  refine ⟨j + 1, hcast, by omega, ?_⟩
  have hgt : ∀ y ∈ cfg.bag, (j : Int) < y := by
    intro y hy
    have := h_ge y hy
    omega
  have hmem' : ((j : Nat) : Int) + 1 ∈ cfg.bag := by rw [hj]; exact h_mem
  rw [System5_run_then_pop cfg j r rest h_rules hgt hmem']
  simp only [hcast]

/-! ## Shifting a whole rule list twice -/

/-- Two uniform increments of a rule list compose. -/
theorem map_shift_comp (l : List (List Int)) (a c : Int) :
    (l.map (fun t => t.map (· + a))).map (fun t => t.map (· + c))
      = l.map (List.map (· + (a + c))) := by
  induction l with
  | nil => rfl
  | cons t rest ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih, List_Int_map_add_compose]

/-! ## The first pop of Smith's run

Common to both head bits: the bag is the pairs of the ascending starts, so
its minimum is the first start `x` and its second smallest element is
`x + g` with `g` the gap of the head bit.  The first `x - 1` steps are pure
decrements, step `x` brings `x` to 0 and pops the first rule of the leading
pair.  That rule sits at least 2 above the counter, hence at least 5 above
every bag integer, so after the shift it is still disjoint from the bag and
the parity merge is an append. -/

/-- The run up to and including the first rule pop, stated for an arbitrary
    gap `g` so that both cases of the per-step lemma use it.  The resulting
    bag is `g` together with the rest of the old bag shifted down by `x`,
    followed by the popped rule shifted up by `x`. -/
theorem System5_run_to_first_pop (s : System5Config) (x g bound : Int)
    (P r1 : List Int) (tl : List (List Int))
    (hx1 : 1 ≤ x) (hperm : s.bag.Perm (x :: (x + g) :: P)) (hnd : s.bag.Nodup)
    (hxle : ∀ y ∈ s.bag, x ≤ y) (hbound : ∀ y ∈ s.bag, y + 3 ≤ bound)
    (hr1ge : ∀ v ∈ r1, bound + 2 ≤ v) (hr1nd : r1.Nodup)
    (hrules : s.rules = r1 :: tl) :
    ∃ (k : Nat) (s' : System5Config), (k : Int) = x ∧ 1 ≤ k ∧
      System5.nSteps s k = some s' ∧
      s'.bag.Perm ((g :: P.map (· - x)) ++ r1.map (· + x)) ∧
      s'.bag.Nodup ∧
      s'.rules = tl.map (fun t => t.map (· + x)) := by
  have hxmem : x ∈ s.bag := hperm.mem_iff.mpr (by simp)
  obtain ⟨k, hk, hkpos, hrun⟩ := System5_run_then_pop_int s x hx1 r1 tl hrules hxle hxmem
  have hR1ge : ∀ v ∈ r1.map (· + x), bound + 2 + x ≤ v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    have := hr1ge u hu
    omega
  have hB1le : ∀ y ∈ (s.bag.map (· - x)).erase 0, y ≤ bound - 3 - x := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_of_mem_erase hy)
    have := hbound z hz
    omega
  have hR1nd : (r1.map (· + x)).Nodup :=
    nodup_map_of_injective _ (fun u v huv => by omega) hr1nd
  have hdisj : ∀ v ∈ r1.map (· + x), v ∉ (s.bag.map (· - x)).erase 0 := by
    intro v hv hmem
    have h1 := hR1ge v hv
    have h2 := hB1le v hmem
    omega
  have hB1nd : ((s.bag.map (· - x)).erase 0).Nodup :=
    List.Nodup.erase _ (nodup_map_of_injective _ (fun u v huv => by omega) hnd)
  have hB1perm : ((s.bag.map (· - x)).erase 0).Perm (g :: P.map (· - x)) := by
    have h1 : (s.bag.map (· - x)).Perm ((x :: (x + g) :: P).map (· - x)) := hperm.map _
    have h2 : ((x :: (x + g) :: P).map (· - x)) = (0 : Int) :: g :: P.map (· - x) := by
      simp only [List.map_cons]
      rw [show x - x = (0 : Int) from by omega, show x + g - x = g from by omega]
    rw [h2] at h1
    have h3 := h1.erase (0 : Int)
    rwa [List.erase_cons_head] at h3
  exact ⟨k, _, hk, hkpos, hrun,
    (xorMerge_perm_append _ _ hR1nd hdisj).trans (hB1perm.append_right _),
    xorMerge_nodup _ _ hB1nd, rfl⟩

/-! ## The per-step lemma, 0-head case

Smith's run, TM23Proof.pdf p. 19-20.  Write the bag as the pairs of the
ascending starts `x :: a'`, the leading rule pair as `r1 = r2 + 2` encoded
from the counter `i`, and let `i'` be the counter the leading appendant ends
at.

Steps `1 .. x - 1` are pure decrements: the smallest bag integer is `x`, so
nothing reaches 0.  Step `x` brings the first start to 0, pops `r1 + x` and
merges it into the bag; every integer of `r1 + x` is at least `i + 2 + x`
while every surviving bag integer is at most `i - 3 - x`, so the merge is an
append.  Step `x + 1` brings the second integer of the consumed pair, which
is `x + 1` because the bit is a `0`, to 0 and pops `r2 + (x + 1)`; that list
is exactly `(r1 + x) - 1`, the block the previous pop appended, so the merge
deletes it.  What survives is the rest of the bag shifted down by `x + 1`,
which is the family of pairs of `a' - (x + 1)`, and the rule list is the
remaining blocks shifted up by `x + 1`, i.e. the canonical layout from the
counter `i' + (x + 1)`.  The threshold `y + 3 <= i' + (x + 1)` follows from
`y + 3 <= i <= i'`. -/

/-- One step of a doubled cyclic tag system whose working string begins with
    a `0` is emulated by `x + 1` steps of System 5, where `x` is the
    smallest bag integer.  The budget drops by one appendant and the phase
    advances by one, reduced modulo the number of appendants exactly as
    `CTS.step` reduces it.

    The time-pinned form: the step count is named, and `x` is exhibited as a
    bag element below every bag element, which is what fixes the schedule of
    the `ForwardSim` lifting. -/
theorem represents_step_false_time (C : CTS) (w : List Bool) (p n : Nat)
    (s : System5Config)
    (h : Represents s C { data := false :: w, phase := p } (n + 1)) :
    ∃ (k : Nat) (x : Int), 1 ≤ x ∧ (k : Int) = x + 1 ∧
      x ∈ s.bag ∧ (∀ y ∈ s.bag, x ≤ y) ∧
      ∃ s', System5.nSteps s k = some s' ∧
        Represents s' C { data := w, phase := (p + 1) % C.appendants.length } n := by
  obtain ⟨x, a', i, i', r1, r2, rest, hx1, hasc, hperm, hxle, hbound, -, hr12,
    hr2ge, hr2nd, hii', hrules⟩ := Represents_cons_decomp C false w p n s h
  rw [show gap false = 1 from rfl] at hasc hperm
  have hbagnd : s.bag.Nodup := Represents_bag_nodup s C _ _ h
  have hxmem : x ∈ s.bag := hperm.mem_iff.mpr (by simp)
  have hPmem : ∀ z ∈ pairsOf w a', z ∈ s.bag := by
    intro z hz
    exact hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
  have hPle : ∀ z ∈ pairsOf w a', z + 3 ≤ i := fun z hz => hbound z (hPmem z hz)
  have hr1ge : ∀ v ∈ r1, i + 2 ≤ v := by
    intro v hv
    rw [hr12] at hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    have := hr2ge t ht
    omega
  have hr1nd : r1.Nodup := by
    rw [hr12]
    exact nodup_map_of_injective _ (fun u v huv => by omega) hr2nd
  -- Steps 1 .. x: the pure decrements and the pop of the first rule.
  obtain ⟨k1, cfg1, hk1, hk1pos, hrun1, hcfg1perm, hcfg1nd, hcfg1rules⟩ :=
    System5_run_to_first_pop s x 1 i (pairsOf w a') r1
      (r2 :: ((ruleBlocks (appendantsFrom C (p + 1) n) i').1 ++ rest))
      hx1 hperm hbagnd hxle hbound hr1ge hr1nd hrules
  -- Step x + 1: the second rule of the pair cancels what the first added.
  have hone : (1 : Int) ∈ cfg1.bag := hcfg1perm.mem_iff.mpr (by simp)
  have hqnd : (r2.map (· + (x + 1))).Nodup :=
    nodup_map_of_injective _ (fun u v huv => by omega) hr2nd
  have hR1sub : (r1.map (· + x)).map (· - 1) = r2.map (· + (x + 1)) := by
    rw [hr12]
    simp only [List.map_map]
    refine List.map_congr_left ?_
    intro t _
    simp only [Function.comp_apply]
    omega
  have hperm2 : ((cfg1.bag.map (· - 1)).erase 0).Perm
        ((pairsOf w a').map (· - (x + 1)) ++ r2.map (· + (x + 1))) := by
    have h1 := (hcfg1perm.map (· - 1)).erase (0 : Int)
    have h2 : (((1 : Int) :: (pairsOf w a').map (· - x)) ++ r1.map (· + x)).map (· - 1)
        = (0 : Int) :: (((pairsOf w a').map (· - x)).map (· - 1)
                         ++ (r1.map (· + x)).map (· - 1)) := by
      rw [List.cons_append]
      simp only [List.map_cons, List.map_append]
      rw [show (1 : Int) - 1 = 0 from by omega]
    rw [h2, List.erase_cons_head, List_Int_map_sub_compose, hR1sub] at h1
    exact h1
  have hdisj2 : ∀ y ∈ r2.map (· + (x + 1)), y ∉ (pairsOf w a').map (· - (x + 1)) := by
    intro y hy hmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    obtain ⟨z, hz, hzeq⟩ := List.mem_map.mp hmem
    have h1 := hr2ge t ht
    have h2 := hPle z hz
    omega
  have hrpop : (((r2.map (· + x)).map (· + 1))).Perm (r2.map (· + (x + 1))) := by
    rw [List_Int_map_add_compose]
  obtain ⟨cfg2, hstep2, hbag2, hrules2⟩ :=
    System5_step_pop_perm_cancel cfg1 (r2.map (· + x))
      (((ruleBlocks (appendantsFrom C (p + 1) n) i').1 ++ rest).map (fun t => t.map (· + x)))
      ((pairsOf w a').map (· - (x + 1))) (r2.map (· + (x + 1)))
      (by rw [hcfg1rules, List.map_cons]) hone hcfg1nd hqnd hperm2 hdisj2 hrpop
  have hrun : System5.nSteps s (k1 + 1) = some cfg2 := by
    rw [System5.nSteps_add, hrun1, Option.bind_some, System5.nSteps_one, hstep2]
  refine ⟨k1 + 1, x, hx1, by push_cast; omega, hxmem, hxle,
          cfg2, hrun, ⟨a'.map (· - (x + 1)), ?_, ?_⟩,
          i' + (x + 1), rest.map (List.map (· + (x + 1))), ?_, ?_⟩
  · have hA := pairsAsc_map_sub (x + 1) w a' (x + 1) hasc
    rwa [show x + 1 - (x + 1) = (0 : Int) from by omega] at hA
  · show cfg2.bag.Perm (pairsOf w (a'.map (· - (x + 1))))
    rw [pairsOf_map_sub]
    exact hbag2
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (hbag2.mem_iff.mp hy)
    have := hPle z hz
    omega
  · show cfg2.rules = _
    rw [hrules2, map_shift_comp, List.map_append, appendantsFrom_mod, ruleBlocks_shift]

/-- The per-step lemma in the shape PLAN.md section 3 asks for: one cyclic
    tag step is emulated by at least one System 5 step, with the relation
    re-established at one appendant less of budget. -/
theorem represents_step_false (C : CTS) (w : List Bool) (p n : Nat) (s : System5Config)
    (h : Represents s C { data := false :: w, phase := p } (n + 1)) :
    ∃ k, 1 ≤ k ∧ ∃ s', System5.nSteps s k = some s' ∧
      Represents s' C { data := w, phase := (p + 1) % C.appendants.length } n := by
  obtain ⟨k, x, hx1, hkx, -, -, s', hrun, hrep⟩ := represents_step_false_time C w p n s h
  exact ⟨k, by omega, s', hrun, hrep⟩

/-! ## The appendant a 1-head step appends

A 1-head step of a doubled cyclic tag system appends the current appendant,
which is `dbl a` for some `a`, to the working string.  On the System 5 side
the two pops of the leading rule pair put `r2 + x` and `r2 + (x + 2)` into
the bag, and those two blocks together are the canonical bag of `a` laid out
from the rule counter shifted by `x`: a doubled `1` contributes the second
rule integers `q, q + 3`, hence the bag integers `q + x, q + x + 3` and
`q + x + 2, q + x + 5`, and a doubled `0` contributes `q, q + 1`, hence
`q + x, q + x + 1` and `q + x + 2, q + x + 3`. -/

/-- Four blocks regroup: what the two pops deposit interleaved is what the
    canonical layout lists in one piece. -/
theorem perm_append_shuffle (A X B Y : List Int) :
    ((A ++ X) ++ (B ++ Y)).Perm ((A ++ B) ++ (X ++ Y)) := by
  simp only [List.append_assoc]
  refine List.Perm.append_left A ?_
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.Perm.append_right Y List.perm_append_comm

/-- The rule counter an appendant encoding ends at, as the `cy2s5.pl`
    counter fold: 6 per `1` and 4 per `0`. -/
theorem encodeAppendant_counter (a : List Bool) (i : Int) :
    (encodeAppendant a i).2.2
      = a.foldl (fun acc b => acc + if b then (6 : Int) else 4) i := by
  induction a generalizing i with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | true =>
      show (encodeAppendant rest (i + 6)).2.2 = _
      rw [ih (i + 6)]
      simp
    | false =>
      show (encodeAppendant rest (i + 4)).2.2 = _
      rw [ih (i + 4)]
      simp

/-- The two shifted copies of the second rule of an appendant pair, the one
    the first pop left in the bag and the one the second pop adds, are
    together the canonical bag of that appendant. -/
theorem encodeAppendant_snd_bag_perm (a : List Bool) (i m : Int) :
    ((encodeAppendant a i).2.1.map (· + m)
       ++ (encodeAppendant a i).2.1.map (· + (m + 2))).Perm
      (ctsConfigToSystem5BagAux a (i + m)) := by
  induction a generalizing i with
  | nil => exact List.Perm.refl _
  | cons b rest ih =>
    cases b with
    | true =>
      show ((((i : Int) :: (i + 3) :: (encodeAppendant rest (i + 6)).2.1).map (· + m))
              ++ (((i : Int) :: (i + 3) :: (encodeAppendant rest (i + 6)).2.1).map
                    (· + (m + 2)))).Perm
           ((i + m) :: (i + m + 2) :: (i + m + 3) :: (i + m + 5) ::
              ctsConfigToSystem5BagAux rest (i + m + 6))
      simp only [List.map_cons]
      refine (perm_append_shuffle [i + m, i + 3 + m] _ [i + (m + 2), i + 3 + (m + 2)] _).trans ?_
      have h4 : (([i + m, i + 3 + m] ++ [i + (m + 2), i + 3 + (m + 2)]) : List Int).Perm
          [i + m, i + m + 2, i + m + 3, i + m + 5] := by
        rw [show (i : Int) + 3 + m = i + m + 3 from by omega,
            show (i : Int) + (m + 2) = i + m + 2 from by omega,
            show (i : Int) + 3 + (m + 2) = i + m + 5 from by omega]
        exact List.Perm.cons _ (List.Perm.swap _ _ _)
      refine List.Perm.append h4 ?_
      have hi := ih (i + 6)
      rwa [show (i : Int) + 6 + m = i + m + 6 from by omega] at hi
    | false =>
      show ((((i : Int) :: (i + 1) :: (encodeAppendant rest (i + 4)).2.1).map (· + m))
              ++ (((i : Int) :: (i + 1) :: (encodeAppendant rest (i + 4)).2.1).map
                    (· + (m + 2)))).Perm
           ((i + m) :: (i + m + 1) :: (i + m + 2) :: (i + m + 3) ::
              ctsConfigToSystem5BagAux rest (i + m + 4))
      simp only [List.map_cons]
      refine (perm_append_shuffle [i + m, i + 1 + m] _ [i + (m + 2), i + 1 + (m + 2)] _).trans ?_
      have h4 : (([i + m, i + 1 + m] ++ [i + (m + 2), i + 1 + (m + 2)]) : List Int).Perm
          [i + m, i + m + 1, i + m + 2, i + m + 3] := by
        rw [show (i : Int) + 1 + m = i + m + 1 from by omega,
            show (i : Int) + (m + 2) = i + m + 2 from by omega,
            show (i : Int) + 1 + (m + 2) = i + m + 3 from by omega]
        exact List.Perm.refl _
      refine List.Perm.append h4 ?_
      have hi := ih (i + 4)
      rwa [show (i : Int) + 4 + m = i + m + 4 from by omega] at hi

/-- Every integer of the canonical bag of an appendant lies strictly below
    the counter its encoding ends at, both shifted alike.  This is the
    threshold clause of the 1-head case, and it is met with equality. -/
theorem encodeAppendant_bagAux_lt (a : List Bool) (i m : Int) :
    ∀ y ∈ ctsConfigToSystem5BagAux a (i + m), y + 1 ≤ (encodeAppendant a i).2.2 + m := by
  intro y hy
  have h1 := bagAux_lt_counter a (i + m) y hy
  have h2 := foldl_counter_init_shift a i m
  rw [h2] at h1
  rw [encodeAppendant_counter]
  exact h1

/-- Every appendant of a doubled system is a doubled word: the doubled
    appendant at an even phase, the blank one at an odd phase. -/
theorem double_currentAppendant_dbl (C : CTS) (p : Nat) :
    ∃ a : List Bool, (double C).currentAppendant p = dbl a := by
  obtain ⟨t, ht | ht⟩ : ∃ t : Nat, p = 2 * t ∨ p = 2 * t + 1 := ⟨p / 2, by omega⟩
  · exact ⟨C.currentAppendant t, by rw [ht, double_currentAppendant_even]⟩
  · exact ⟨[], by rw [ht, double_currentAppendant_odd]; rfl⟩

/-! ## Splitting a bag at a concatenation of working strings -/

/-- The bag of a concatenation splits when the starts split at the same
    place.  The length hypothesis is load-bearing: with a longer first block
    of starts the second working string reads the wrong ones. -/
theorem pairsOf_append (w1 w2 : List Bool) (a1 a2 : List Int)
    (h : a1.length = w1.length) :
    pairsOf (w1 ++ w2) (a1 ++ a2) = pairsOf w1 a1 ++ pairsOf w2 a2 := by
  induction w1 generalizing a1 with
  | nil =>
    cases a1 with
    | nil => rfl
    | cons x t => simp at h
  | cons b w1 ih =>
    cases a1 with
    | nil => simp at h
    | cons x a1 =>
      simp only [List.cons_append, pairsOf_cons]
      rw [ih a1 (by simpa using h)]

/-- The ascending condition of a concatenation: the first block ascends from
    `lo`, its pairs all end below `hi`, and the second block ascends from
    `hi`. -/
theorem pairsAsc_append (lo hi : Int) (w1 w2 : List Bool) (a1 a2 : List Int)
    (hle : lo ≤ hi) (h1 : pairsAsc lo w1 a1 = true)
    (hlt : ∀ y ∈ pairsOf w1 a1, y < hi) (h2 : pairsAsc hi w2 a2 = true) :
    pairsAsc lo (w1 ++ w2) (a1 ++ a2) = true := by
  induction w1 generalizing lo a1 with
  | nil =>
    cases a1 with
    | nil => exact pairsAsc_mono hi lo w2 a2 hle h2
    | cons x t => simp at h1
  | cons b w1 ih =>
    cases a1 with
    | nil => simp at h1
    | cons x a1 =>
      rw [pairsAsc_cons_cons, Bool.and_eq_true, decide_eq_true_eq] at h1
      have hmem : x + gap b ∈ pairsOf (b :: w1) (x :: a1) := by
        rw [pairsOf_cons]
        exact List.mem_cons_of_mem _ (List.mem_cons_self)
      have hxg : x + gap b ≤ hi := le_of_lt (hlt _ hmem)
      have hsub : ∀ y ∈ pairsOf w1 a1, y < hi := by
        intro y hy
        refine hlt y ?_
        rw [pairsOf_cons]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)
      show (decide (lo < x) && pairsAsc (x + gap b) (w1 ++ w2) (a1 ++ a2)) = true
      rw [ih (x + gap b) a1 hxg h1.2 hsub]
      simp only [Bool.and_true, decide_eq_true_eq]
      exact h1.1

/-! ## The per-step lemma, 1-head case

Smith's run again, TM23Proof.pdf p. 19-20, with the leading bit a `1`, so
the pair of the consumed bit is `x, x + 2`.

Steps `1 .. x` are as in the 0-head case: pure decrements until step `x`,
which brings the first start to 0 and appends `r1 + x` to the bag.  Step
`x + 1` is now a pure decrement, since the second integer of the consumed
pair has only reached 1 at that point.  Step `x + 2` brings it to 0 and pops
`r2 + (x + 2)`.  The block the first pop added has become `r2 + x` by then,
and no two integers of `r2` are exactly 2 apart, so the two blocks are
disjoint and the parity merge is again an append.

Together `r2 + x` and `r2 + (x + 2)` are the canonical bag of the appendant
`a` laid out from `i + x`, i.e. the pairs of `dbl a` over the starts
`startsOf a (i + x)`, which sit above the whole of the old bag shifted down
by `x + 2`.  So the new bag is the family of pairs of
`(a' - (x + 2)) ++ startsOf a (i + x)` over the working string
`w ++ dbl a`, which is exactly what `CTS.step` produces.  The threshold is
met with equality: the last integer of the appended bag is `i' + x - 1` and
the new counter is `i' + (x + 2)`.

The empty appendant is covered by the same proof: `r1 = r2 = []` and
`i' = i`, both pops merge nothing, and `dbl [] = []` leaves the working
string unchanged.  That is the odd-phase case of a doubled system. -/

/-- One step of a doubled cyclic tag system whose working string begins with
    a `1` is emulated by `x + 2` steps of System 5, where `x` is the
    smallest bag integer.  The appendant must be a doubled word, which is
    what `double_currentAppendant_dbl` supplies for a doubled system.

    The time-pinned form: the step count is named, and `x` is exhibited as a
    bag element below every bag element. -/
theorem represents_step_true_time (C : CTS) (w : List Bool) (p n : Nat) (s : System5Config)
    (a : List Bool) (happ : C.currentAppendant p = dbl a)
    (h : Represents s C { data := true :: w, phase := p } (n + 1)) :
    ∃ (k : Nat) (x : Int), 1 ≤ x ∧ (k : Int) = x + 2 ∧
      x ∈ s.bag ∧ (∀ y ∈ s.bag, x ≤ y) ∧
      ∃ s', System5.nSteps s k = some s' ∧
        Represents s' C { data := w ++ dbl a,
                          phase := (p + 1) % C.appendants.length } n := by
  obtain ⟨x, a', i, i', r1, r2, rest, hx1, hasc, hperm, hxle, hbound, henc, hr12,
    hr2ge, hr2nd, hii', hrules⟩ := Represents_cons_decomp C true w p n s h
  rw [show gap true = 2 from rfl] at hasc hperm
  have hbagnd : s.bag.Nodup := Represents_bag_nodup s C _ _ h
  have hxmem : x ∈ s.bag := hperm.mem_iff.mpr (by simp)
  have hix : x + 3 ≤ i := hbound x hxmem
  have hPmem : ∀ z ∈ pairsOf w a', z ∈ s.bag := by
    intro z hz
    exact hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
  have hPle : ∀ z ∈ pairsOf w a', z + 3 ≤ i := fun z hz => hbound z (hPmem z hz)
  have hPgt : ∀ z ∈ pairsOf w a', x + 2 < z := pairsOf_gt (x + 2) w a' hasc
  have hr1ge : ∀ v ∈ r1, i + 2 ≤ v := by
    intro v hv
    rw [hr12] at hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    have := hr2ge t ht
    omega
  have hr1nd : r1.Nodup := by
    rw [hr12]
    exact nodup_map_of_injective _ (fun u v huv => by omega) hr2nd
  have hr2gap : ∀ u ∈ r2, ∀ v ∈ r2, u + 2 ≠ v := by
    have hg := encodePaired_snd_no_gap_two (C.currentAppendant p) i
    rw [henc] at hg
    exact hg
  have hea : encodeAppendant a i = (r1, r2, i') := by
    rw [← encodePaired_dbl, ← happ]
    exact henc
  have hr2eq : (encodeAppendant a i).2.1 = r2 := by rw [hea]
  have hi'eq : (encodeAppendant a i).2.2 = i' := by rw [hea]
  -- Steps 1 .. x: the pure decrements and the pop of the first rule.
  obtain ⟨k1, cfg1, hk1, hk1pos, hrun1, hcfg1perm, hcfg1nd, hcfg1rules⟩ :=
    System5_run_to_first_pop s x 2 i (pairsOf w a') r1
      (r2 :: ((ruleBlocks (appendantsFrom C (p + 1) n) i').1 ++ rest))
      hx1 hperm hbagnd hxle hbound hr1ge hr1nd hrules
  have hcfg1rules' : cfg1.rules
      = r2.map (· + x) ::
          ((ruleBlocks (appendantsFrom C (p + 1) n) i').1 ++ rest).map
            (fun t => t.map (· + x)) := by
    rw [hcfg1rules, List.map_cons]
  have hge2 : ∀ y ∈ cfg1.bag, (2 : Int) ≤ y := by
    intro y hy
    have hy' := hcfg1perm.subset hy
    rw [List.cons_append] at hy'
    rcases List.mem_cons.mp hy' with rfl | hy'
    · omega
    rcases List.mem_append.mp hy' with hy' | hy'
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy'
      have := hPgt z hz
      omega
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy'
      have := hr1ge v hv
      omega
  have hmem2 : (2 : Int) ∈ cfg1.bag := hcfg1perm.mem_iff.mpr (by simp)
  -- Steps x + 1 and x + 2: one pure decrement and the pop of the second rule.
  obtain ⟨k2, hk2, hk2pos, hrun2⟩ :=
    System5_run_then_pop_int cfg1 2 (by omega) (r2.map (· + x))
      (((ruleBlocks (appendantsFrom C (p + 1) n) i').1 ++ rest).map (fun t => t.map (· + x)))
      hcfg1rules' hge2 hmem2
  have hrun : System5.nSteps s (k1 + k2)
      = some { bag := xorMerge ((cfg1.bag.map (· - 2)).erase 0) ((r2.map (· + x)).map (· + 2)),
               rules := ((((ruleBlocks (appendantsFrom C (p + 1) n) i').1 ++ rest).map
                            (fun t => t.map (· + x)))).map (fun t => t.map (· + 2)) } := by
    rw [System5.nSteps_add, hrun1, Option.bind_some, hrun2]
  have hR1 : (r1.map (· + x)).map (· - 2) = r2.map (· + x) := by
    rw [hr12]
    simp only [List.map_map]
    refine List.map_congr_left ?_
    intro t _
    simp only [Function.comp_apply]
    omega
  have hB : ((cfg1.bag.map (· - 2)).erase 0).Perm
      ((pairsOf w a').map (· - (x + 2)) ++ r2.map (· + x)) := by
    have h1 := (hcfg1perm.map (· - (2 : Int))).erase (0 : Int)
    have h2 : ((((2 : Int) :: (pairsOf w a').map (· - x)) ++ r1.map (· + x)).map (· - 2))
        = (0 : Int) :: (((pairsOf w a').map (· - x)).map (· - 2)
                          ++ (r1.map (· + x)).map (· - 2)) := by
      rw [List.cons_append]
      simp only [List.map_cons, List.map_append]
      rw [show (2 : Int) - 2 = 0 from by omega]
    rw [h2, List.erase_cons_head, List_Int_map_sub_compose, hR1] at h1
    exact h1
  have hqnd : (r2.map (· + (x + 2))).Nodup :=
    nodup_map_of_injective _ (fun u v huv => by omega) hr2nd
  have hdisj : ∀ y ∈ r2.map (· + (x + 2)), y ∉ (cfg1.bag.map (· - 2)).erase 0 := by
    intro y hy hmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    rcases List.mem_append.mp (hB.subset hmem) with hm | hm
    · obtain ⟨z, hz, hzeq⟩ := List.mem_map.mp hm
      have h1 := hr2ge t ht
      have h2 := hPle z hz
      omega
    · obtain ⟨u, hu, hueq⟩ := List.mem_map.mp hm
      exact hr2gap t ht u hu (by omega)
  have hbag2 : (xorMerge ((cfg1.bag.map (· - 2)).erase 0) ((r2.map (· + x)).map (· + 2))).Perm
      ((pairsOf w a').map (· - (x + 2)) ++ ctsConfigToSystem5BagAux a (i + x)) := by
    rw [List_Int_map_add_compose]
    refine (xorMerge_perm_append _ _ hqnd hdisj).trans ?_
    refine (hB.append_right _).trans ?_
    rw [List.append_assoc]
    refine List.Perm.append_left _ ?_
    have hbp := encodeAppendant_snd_bag_perm a i x
    rw [hr2eq] at hbp
    exact hbp
  refine ⟨k1 + k2, x, hx1, by push_cast; omega, hxmem, hxle, _, hrun,
          ⟨a'.map (· - (x + 2)) ++ startsOf a (i + x), ?_, ?_⟩,
          i' + (x + 2), rest.map (List.map (· + (x + 2))), ?_, ?_⟩
  · show pairsAsc 0 (w ++ dbl a) (a'.map (· - (x + 2)) ++ startsOf a (i + x)) = true
    refine pairsAsc_append 0 (i + x - 1) w (dbl a) (a'.map (· - (x + 2))) (startsOf a (i + x))
      (by omega) ?_ ?_ (pairsAsc_dbl_startsOf a (i + x - 1) (i + x) (by omega))
    · have hA := pairsAsc_map_sub (x + 2) w a' (x + 2) hasc
      rwa [show x + 2 - (x + 2) = (0 : Int) from by omega] at hA
    · intro y hy
      rw [pairsOf_map_sub] at hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      have := hPle z hz
      omega
  · show (xorMerge ((cfg1.bag.map (· - 2)).erase 0) ((r2.map (· + x)).map (· + 2))).Perm
      (pairsOf (w ++ dbl a) (a'.map (· - (x + 2)) ++ startsOf a (i + x)))
    rw [pairsOf_append w (dbl a) (a'.map (· - (x + 2))) (startsOf a (i + x))
          (by rw [List.length_map]; exact pairsAsc_length (x + 2) w a' hasc),
        pairsOf_map_sub, pairsOf_dbl_startsOf]
    exact hbag2
  · intro y hy
    rcases List.mem_append.mp (hbag2.subset hy) with hm | hm
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hm
      have := hPle z hz
      omega
    · have hb := encodeAppendant_bagAux_lt a i x y hm
      rw [hi'eq] at hb
      omega
  · show (((ruleBlocks (appendantsFrom C (p + 1) n) i').1 ++ rest).map
            (fun t => t.map (· + x))).map (fun t => t.map (· + 2))
        = (ruleBlocks (appendantsFrom C ((p + 1) % C.appendants.length) n) (i' + (x + 2))).1
            ++ rest.map (List.map (· + (x + 2)))
    rw [map_shift_comp, List.map_append, appendantsFrom_mod, ruleBlocks_shift]

/-- The 1-head per-step lemma in the shape PLAN.md section 3 asks for. -/
theorem represents_step_true (C : CTS) (w : List Bool) (p n : Nat) (s : System5Config)
    (a : List Bool) (happ : C.currentAppendant p = dbl a)
    (h : Represents s C { data := true :: w, phase := p } (n + 1)) :
    ∃ k, 1 ≤ k ∧ ∃ s', System5.nSteps s k = some s' ∧
      Represents s' C { data := w ++ dbl a,
                        phase := (p + 1) % C.appendants.length } n := by
  obtain ⟨k, x, hx1, hkx, -, -, s', hrun, hrep⟩ :=
    represents_step_true_time C w p n s a happ h
  exact ⟨k, by omega, s', hrun, hrep⟩

/-! ## The per-step lemma over a doubled system -/

/-- The per-step lemma of link B at a nonempty working string, with the step
    count pinned: the run lasts `x + gap b` steps, where `x` is the smallest
    bag integer and `b` the leading bit, and `x` is exhibited as a bag
    element below every bag element.  This is the form a strictly increasing
    `IsSimSchedule` is built from. -/
theorem represents_step_double_time (C0 : CTS) (b : Bool) (w : List Bool) (p n : Nat)
    (s : System5Config)
    (h : Represents s (double C0) { data := b :: w, phase := p } (n + 1)) :
    ∃ (k : Nat) (x : Int), 1 ≤ x ∧ (k : Int) = x + gap b ∧
      x ∈ s.bag ∧ (∀ y ∈ s.bag, x ≤ y) ∧
      ∃ s', System5.nSteps s k = some s' ∧
        ∃ c', (double C0).step { data := b :: w, phase := p } = some c' ∧
          Represents s' (double C0) c' n := by
  cases b with
  | false =>
    obtain ⟨k, x, hx1, hkx, hxmem, hxle, s', hrun, hrep⟩ :=
      represents_step_false_time (double C0) w p n s h
    exact ⟨k, x, hx1, by rw [show gap false = (1 : Int) from rfl]; exact hkx, hxmem, hxle,
      s', hrun, _, CTS_step_cons (double C0) false w p, hrep⟩
  | true =>
    obtain ⟨a, ha⟩ := double_currentAppendant_dbl C0 p
    obtain ⟨k, x, hx1, hkx, hxmem, hxle, s', hrun, hrep⟩ :=
      represents_step_true_time (double C0) w p n s a ha h
    refine ⟨k, x, hx1, by rw [show gap true = (2 : Int) from rfl]; exact hkx, hxmem, hxle,
      s', hrun, _, CTS_step_cons (double C0) true w p, ?_⟩
    show Represents s' (double C0)
      { data := w ++ (double C0).currentAppendant p,
        phase := (p + 1) % (double C0).appendants.length } n
    rw [ha]
    exact hrep

/-- The per-step lemma of link B, both head bits at once: a System 5
    configuration representing a doubled cyclic tag system at a nonempty
    working string runs for at least one step into a configuration
    representing the cyclic tag step of that configuration, with one
    appendant less of budget.

    The hypothesis that the system is doubled is used exactly once, through
    `double_currentAppendant_dbl`: the 1-head case needs the appendant it
    appends to be a doubled word. -/
theorem represents_step_double (C0 : CTS) (c : CTSConfig) (n : Nat) (s : System5Config)
    (hne : c.data ≠ [])
    (h : Represents s (double C0) c (n + 1)) :
    ∃ k, 1 ≤ k ∧ ∃ s', System5.nSteps s k = some s' ∧
      ∃ c', (double C0).step c = some c' ∧ Represents s' (double C0) c' n := by
  obtain ⟨data, p⟩ := c
  cases data with
  | nil => exact absurd rfl hne
  | cons b w =>
    obtain ⟨k, x, hx1, hkx, -, -, s', hrun, c', hstep, hrep⟩ :=
      represents_step_double_time C0 b w p n s h
    have hg := gap_pos b
    exact ⟨k, by omega, s', hrun, c', hstep, hrep⟩

/-! ## The TM23Proof.pdf p. 29 instance

The `cy2s5.pl 3 01 1 10` program of TM23Proof.pdf p. 29: bag
`1,2,3,4,5,7,8,10`, eight rules, representing the doubled cyclic tag system
`11 "" 1100 ""` in the configuration `0011` at phase 0 (`exCTS`, `exCfg` and
`ex_represents` of `Smith.Represents`).

Its working string begins with a `0` and its smallest bag integer is 1, so
the per-step lemma predicts two System 5 steps per cyclic tag step.  Both
the run and the re-established relation are pinned by `decide`, twice in a
row, which is also the `decide` regression asked for by PLAN.md M2. -/

/-- Two System 5 steps of the p. 29 program.  The bag is the pairs of the
    starts `1, 3, 6` of the working string `011` and the rules are the
    canonical layout from the counter 21. -/
theorem ex_pdf29_two_steps :
    System5.nSteps (ctsToSystem5 exCTS exCfg 1) 2
      = some { bag := [1, 2, 3, 5, 6, 8],
               rules := [[], [], [23, 26, 29, 30], [21, 24, 27, 28], [], []] } := by
  decide

/-- The bag after two steps decodes to the working string the doubled
    system reaches after one step. -/
theorem ex_pdf29_two_steps_decode :
    decodeBag [1, 2, 3, 5, 6, 8] = some [false, true, true] := by decide

/-- The configuration after two steps represents the doubled system one step
    on, at phase 1, with one appendant less of budget. -/
theorem ex_represents_after_two :
    Represents { bag := [1, 2, 3, 5, 6, 8],
                 rules := [[], [], [23, 26, 29, 30], [21, 24, 27, 28], [], []] }
      (double exCTS) { data := [false, true, true], phase := 1 } 3 :=
  ⟨⟨[1, 3, 6], by decide, by decide⟩, ⟨21, [], by decide, by decide⟩⟩

/-- Four System 5 steps of the p. 29 program: two more steps consume the
    second `0` of the doubled working string. -/
theorem ex_pdf29_four_steps :
    System5.nSteps (ctsToSystem5 exCTS exCfg 1) 4
      = some { bag := [1, 3, 4, 6],
               rules := [[25, 28, 31, 32], [23, 26, 29, 30], [], []] } := by
  decide

/-- The bag after four steps decodes to `11`. -/
theorem ex_pdf29_four_steps_decode :
    decodeBag [1, 3, 4, 6] = some [true, true] := by decide

/-- The configuration after four steps represents the doubled system two
    steps on, at phase 2. -/
theorem ex_represents_after_four :
    Represents { bag := [1, 3, 4, 6],
                 rules := [[25, 28, 31, 32], [23, 26, 29, 30], [], []] }
      (double exCTS) { data := [true, true], phase := 2 } 2 :=
  ⟨⟨[1, 4], by decide, by decide⟩, ⟨23, [], by decide, by decide⟩⟩

/-- The per-step lemma on the p. 29 program: the first `0` of the doubled
    working string `0011`. -/
theorem ex_step_false_pdf29 :
    ∃ k, 1 ≤ k ∧ ∃ s', System5.nSteps (ctsToSystem5 exCTS exCfg 1) k = some s' ∧
      Represents s' (double exCTS) { data := [false, true, true], phase := 1 } 3 :=
  represents_step_false (double exCTS) [false, true, true] 0 3 _ ex_represents

/-- The per-step lemma again, on the configuration the first application
    produced: the second `0` of `0011`. -/
theorem ex_step_false_pdf29_snd :
    ∃ k, 1 ≤ k ∧ ∃ s',
      System5.nSteps { bag := [1, 2, 3, 5, 6, 8],
                       rules := [[], [], [23, 26, 29, 30], [21, 24, 27, 28], [], []] } k
        = some s' ∧
      Represents s' (double exCTS) { data := [true, true], phase := 2 } 2 :=
  represents_step_false (double exCTS) [true, true] 1 2 _ ex_represents_after_two

/-- The two steps the per-step lemma predicts, pinned: the smallest bag
    integer of the p. 29 program is 1, so `k = x + 1 = 2`. -/
theorem ex_step_false_pdf29_two :
    ∃ s', System5.nSteps (ctsToSystem5 exCTS exCfg 1) 2 = some s' ∧
      Represents s' (double exCTS) { data := [false, true, true], phase := 1 } 3 :=
  ⟨_, ex_pdf29_two_steps, ex_represents_after_two⟩

/-- The same for the second application: two more steps, again with the
    smallest bag integer 1. -/
theorem ex_step_false_pdf29_four :
    ∃ s', System5.nSteps (ctsToSystem5 exCTS exCfg 1) 4 = some s' ∧
      Represents s' (double exCTS) { data := [true, true], phase := 2 } 2 :=
  ⟨_, ex_pdf29_four_steps, ex_represents_after_four⟩

/-- Negative instance: the two steps are both needed.  After one step the
    bag has nine elements and does not decode at all, since the rule the
    first pop appended has not yet been cancelled. -/
theorem ex_pdf29_one_step_no_decode :
    (System5.nSteps (ctsToSystem5 exCTS exCfg 1) 1).map (fun c => decodeBag c.bag)
      = some none := by decide

/-- Negative instance at the level of the relation: the configuration after
    one step represents no cyclic tag configuration with working string
    `011`, whatever the rules and the budget, because the bag clause forces
    two bag integers per bit. -/
theorem ex_pdf29_one_step_not_represents (rules : List (List Int)) (b : Nat) :
    ¬ Represents { bag := [19, 16, 1, 2, 3, 4, 6, 7, 9], rules := rules }
        (double exCTS) { data := [false, true, true], phase := 1 } b := by
  intro hh
  have hlen := Represents_bag_length _ _ _ _ hh
  simp at hlen

/-! ## The TM23Proof.pdf p. 29 instance, 1-head case

The same `cy2s5.pl 3 01 1 10` run, four steps further on.  After four steps
the doubled working string is `11` at phase 2, where the doubled system
reads the appendant `1100 = dbl 10`, and the smallest bag integer is 1, so
the 1-head per-step lemma predicts three System 5 steps and a working string
`1 ++ 1100`.  Three steps after that the appendant is the blank one of the
odd phase 3 and the working string loses its leading `1` and gains nothing.

These are also the `decide` regression asked for by PLAN.md M2: seven and
ten steps of the p. 29 program, matched against the relation. -/

/-- Seven System 5 steps of the p. 29 program: the three the 1-head case
    predicts on top of the four of the two 0-head steps. -/
theorem ex_pdf29_seven_steps :
    System5.nSteps (ctsToSystem5 exCTS exCfg 1) 7
      = some { bag := [33, 32, 29, 26, 31, 30, 27, 24, 1, 3], rules := [[], []] } := by
  decide

/-- The bag after seven steps decodes to the working string `11100` the
    doubled system reaches, the appendant `1100` appended. -/
theorem ex_pdf29_seven_steps_decode :
    decodeBag [33, 32, 29, 26, 31, 30, 27, 24, 1, 3]
      = some [true, true, true, false, false] := by decide

/-- The configuration after seven steps represents the doubled system three
    steps on, at phase 3, with one appendant less of budget.  The starts are
    the old one shifted down by 3 followed by `startsOf 10 24`, and the
    counter is the old `i' = 33` shifted up by 3. -/
theorem ex_represents_after_seven :
    Represents { bag := [33, 32, 29, 26, 31, 30, 27, 24, 1, 3], rules := [[], []] }
      (double exCTS) { data := [true, true, true, false, false], phase := 3 } 1 :=
  ⟨⟨[1, 24, 27, 30, 32], by decide, by decide⟩, ⟨36, [], by decide, by decide⟩⟩

/-- The appendant the doubled p. 29 system reads at phase 2 is the doubled
    appendant `10`, so the 1-head per-step lemma applies there. -/
theorem ex_appendant_phase_two :
    (double exCTS).currentAppendant 2 = dbl [true, false] := by decide

/-- The appendant at the odd phase 3 is the blank one, which is `dbl []`. -/
theorem ex_appendant_phase_three :
    (double exCTS).currentAppendant 3 = dbl [] := by decide

/-- The 1-head per-step lemma on the p. 29 program, applied to the
    configuration four steps in. -/
theorem ex_step_true_pdf29 :
    ∃ k, 1 ≤ k ∧ ∃ s',
      System5.nSteps { bag := [1, 3, 4, 6],
                       rules := [[25, 28, 31, 32], [23, 26, 29, 30], [], []] } k = some s' ∧
      Represents s' (double exCTS)
        { data := [true, true, true, false, false], phase := 3 } 1 :=
  represents_step_true (double exCTS) [true] 2 1 _ [true, false] ex_appendant_phase_two
    ex_represents_after_four

/-- The three steps the lemma predicts, pinned: the smallest bag integer of
    the four-step configuration is 1, so `k = x + 2 = 3`. -/
theorem ex_step_true_pdf29_three :
    ∃ s', System5.nSteps (ctsToSystem5 exCTS exCfg 1) 7 = some s' ∧
      Represents s' (double exCTS)
        { data := [true, true, true, false, false], phase := 3 } 1 :=
  ⟨_, ex_pdf29_seven_steps, ex_represents_after_seven⟩

/-- Ten System 5 steps: three more, for the blank appendant of phase 3. -/
theorem ex_pdf29_ten_steps :
    System5.nSteps (ctsToSystem5 exCTS exCfg 1) 10
      = some { bag := [30, 29, 26, 23, 28, 27, 24, 21], rules := [] } := by
  decide

/-- The bag after ten steps decodes to `1100`. -/
theorem ex_pdf29_ten_steps_decode :
    decodeBag [30, 29, 26, 23, 28, 27, 24, 21] = some [true, true, false, false] := by decide

/-- The configuration after ten steps represents the doubled system four
    steps on, back at phase 0, with the budget exhausted. -/
theorem ex_represents_after_ten :
    Represents { bag := [30, 29, 26, 23, 28, 27, 24, 21], rules := [] }
      (double exCTS) { data := [true, true, false, false], phase := 0 } 0 :=
  ⟨⟨[21, 24, 27, 29], by decide, by decide⟩, ⟨39, [], by decide, by decide⟩⟩

/-- The 1-head per-step lemma again, at the odd phase 3, where the appendant
    is `dbl [] = []` and the working string only loses its leading bit. -/
theorem ex_step_true_pdf29_snd :
    ∃ k, 1 ≤ k ∧ ∃ s',
      System5.nSteps { bag := [33, 32, 29, 26, 31, 30, 27, 24, 1, 3], rules := [[], []] } k
        = some s' ∧
      Represents s' (double exCTS) { data := [true, true, false, false], phase := 0 } 0 :=
  represents_step_true (double exCTS) [true, true, false, false] 3 0 _ []
    ex_appendant_phase_three ex_represents_after_seven

/-- The three further steps, pinned. -/
theorem ex_step_true_pdf29_six :
    ∃ s', System5.nSteps (ctsToSystem5 exCTS exCfg 1) 10 = some s' ∧
      Represents s' (double exCTS) { data := [true, true, false, false], phase := 0 } 0 :=
  ⟨_, ex_pdf29_ten_steps, ex_represents_after_ten⟩

/-- The per-step lemma over a doubled system, on the p. 29 program: the
    cyclic tag step is exhibited, and it is the 1-head one. -/
theorem ex_step_double_pdf29 :
    ∃ k, 1 ≤ k ∧ ∃ s',
      System5.nSteps { bag := [1, 3, 4, 6],
                       rules := [[25, 28, 31, 32], [23, 26, 29, 30], [], []] } k = some s' ∧
      ∃ c', (double exCTS).step { data := [true, true], phase := 2 } = some c' ∧
        Represents s' (double exCTS) c' 1 :=
  represents_step_double exCTS { data := [true, true], phase := 2 } 1 _ (by decide)
    ex_represents_after_four

/-- Negative instance: five steps are not enough.  The bag still carries the
    block the first pop appended and does not decode at all. -/
theorem ex_pdf29_five_steps_no_decode :
    (System5.nSteps (ctsToSystem5 exCTS exCfg 1) 5).map (fun c => decodeBag c.bag)
      = some none := by decide

/-- Negative instance: six steps are not enough either, so the third step of
    the 1-head case is real. -/
theorem ex_pdf29_six_steps_no_decode :
    (System5.nSteps (ctsToSystem5 exCTS exCfg 1) 6).map (fun c => decodeBag c.bag)
      = some none := by decide

/-! ## Examples for the facts the 1-head case rests on -/

/-- Positive instance of the gap condition: the second rule of the pair of
    the appendant `1100` at counter 23 is `23, 26, 29, 30`, whose steps are
    3, 3 and 1. -/
theorem ex_encodeAppendant_pdf29 :
    encodeAppendant [true, false] 23 = ([25, 28, 31, 32], [23, 26, 29, 30], 33) := by decide

/-- Positive instance: the integers of that second rule are 1 apart or at
    least 3 apart. -/
theorem ex_snd_gap_pos :
    ([23, 26, 29, 30] : List Int).Pairwise (fun u v => u + 1 = v ∨ u + 3 ≤ v) := by decide

/-- Negative instance: two integers exactly 2 apart fail the gap condition,
    which is the configuration that would make the second pop cancel instead
    of append. -/
theorem ex_snd_gap_neg :
    ¬ ([1, 3] : List Int).Pairwise (fun u v => u + 1 = v ∨ u + 3 ≤ v) := by decide

/-- Positive instance of `encodeAppendant_snd_bag_perm` at `i = 23`,
    `m = 1`: the two blocks the pops deposit are the canonical bag of the
    appendant `10` from 24. -/
theorem ex_snd_bag_perm :
    (([23, 26, 29, 30].map (· + (1 : Int))
        ++ [23, 26, 29, 30].map (· + (3 : Int))) : List Int).Perm
      (ctsConfigToSystem5BagAux [true, false] 24) := by decide

/-- Negative instance: the second block really is the first shifted by 2.
    Shifted by 1 the two blocks overlap and no longer cover the bag. -/
theorem ex_snd_bag_perm_neg :
    ¬ (([23, 26, 29, 30].map (· + (1 : Int))
        ++ [23, 26, 29, 30].map (· + (2 : Int))) : List Int).Perm
      (ctsConfigToSystem5BagAux [true, false] 24) := by decide

/-- Positive instance of `pairsOf_append`: one start per bit in the first
    block. -/
theorem ex_pairsOf_append_pos :
    pairsOf ([false] ++ [true]) ([1] ++ [5])
      = pairsOf [false] [1] ++ pairsOf [true] [5] := by decide

/-- Negative instance: with one start too many in the first block the split
    reads the wrong starts, so the length hypothesis is load-bearing. -/
theorem ex_pairsOf_append_neg :
    pairsOf ([false] ++ [true]) ([1, 5] ++ [9])
      ≠ pairsOf [false] [1, 5] ++ pairsOf [true] [9] := by decide

/-- Positive instance of `pairsAsc_append`: the second block starts above
    the end of the first. -/
theorem ex_pairsAsc_append_pos :
    pairsAsc 0 ([false] ++ [true]) ([1] ++ [5]) = true := by decide

/-- Negative instance: a second block starting on the end of the first
    fails, which is the bound the 1-head case checks at `i + x`. -/
theorem ex_pairsAsc_append_neg :
    pairsAsc 0 ([false] ++ [true]) ([1] ++ [2]) = false := by decide

end Smith
