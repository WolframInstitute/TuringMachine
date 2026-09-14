/-
  BiTM.XorMerge

  Symmetric-difference (parity-mod-2) list-bag operations used by the
  System 5 reduction in `BiTM.CockeMinskyConstruction`.

  Pure list utilities — no dependency on TM/Tag/CTS machinery.

  Contents:
    * `xorInsert`, `xorMerge` definitions
    * Membership / Nodup lemmas
    * Symmetric-difference characterisation (`xorMerge_mem_iff`)
    * Self-merge → empty (`xorMerge_self_eq_nil`)
-/

namespace BiTM

/-- XOR-insert: if `x` already appears an odd number of times in `xs`,
    remove one occurrence (toggling to even); else add one.  Equivalent
    to "toggle membership" in the parity-mod-2 semantics. -/
def xorInsert (x : Int) (xs : List Int) : List Int :=
  if x ∈ xs then xs.erase x else x :: xs

/-- XOR-merge two multisets under parity semantics: fold `xorInsert`. -/
def xorMerge (xs ys : List Int) : List Int :=
  ys.foldl (fun acc y => xorInsert y acc) xs

/-- Merging an empty rule into a bag preserves the bag. -/
@[simp] theorem xorMerge_nil (xs : List Int) : xorMerge xs [] = xs := by
  simp [xorMerge]

/-- Direct unfold of `xorInsert` when the element is absent. -/
theorem xorInsert_not_mem (x : Int) (xs : List Int) (h : x ∉ xs) :
    xorInsert x xs = x :: xs := by
  unfold xorInsert
  rw [if_neg h]

/-- Direct unfold of `xorInsert` when the element is present. -/
theorem xorInsert_mem (x : Int) (xs : List Int) (h : x ∈ xs) :
    xorInsert x xs = xs.erase x := by
  unfold xorInsert
  rw [if_pos h]

/-- `xorInsert` preserves `Nodup`.  Adding when absent prepends; erasing
    when present uses `List.Nodup.erase`. -/
theorem xorInsert_nodup (x : Int) (xs : List Int) (h : xs.Nodup) :
    (xorInsert x xs).Nodup := by
  by_cases h_mem : x ∈ xs
  · rw [xorInsert_mem _ _ h_mem]
    exact List.Nodup.erase _ h
  · rw [xorInsert_not_mem _ _ h_mem]
    exact List.nodup_cons.mpr ⟨h_mem, h⟩

/-- **Toggle membership of `y`** under `xorInsert y` (Nodup hypothesis).
    `y ∈ xorInsert y xs ↔ y ∉ xs`. -/
theorem xorInsert_mem_self_iff_nodup (y : Int) (xs : List Int) (h : xs.Nodup) :
    y ∈ xorInsert y xs ↔ y ∉ xs := by
  by_cases h_mem : y ∈ xs
  · rw [xorInsert_mem _ _ h_mem]
    constructor
    · intro h_in; exact absurd h_in (List.Nodup.not_mem_erase h)
    · intro h_not; exact absurd h_mem h_not
  · rw [xorInsert_not_mem _ _ h_mem]
    simp [h_mem]

/-- `xorInsert y` only affects membership of `y`: for any `x ≠ y`,
    `x ∈ xorInsert y xs ↔ x ∈ xs`. -/
theorem xorInsert_mem_other_iff
    (y : Int) (xs : List Int) (x : Int) (h_ne : x ≠ y) :
    x ∈ xorInsert y xs ↔ x ∈ xs := by
  by_cases h_mem : y ∈ xs
  · rw [xorInsert_mem _ _ h_mem]
    exact List.mem_erase_of_ne h_ne
  · rw [xorInsert_not_mem _ _ h_mem]
    rw [List.mem_cons]
    constructor
    · rintro (h | h)
      · exact absurd h h_ne
      · exact h
    · exact Or.inr

/-- Cons step for `xorMerge`: peel off the head of the second argument. -/
theorem xorMerge_cons (xs : List Int) (y : Int) (ys : List Int) :
    xorMerge xs (y :: ys) = xorMerge (xorInsert y xs) ys := by
  simp [xorMerge]

/-- Membership-aware cons step: when `y ∈ xs`, peeling `y` erases from xs. -/
theorem xorMerge_cons_mem (xs : List Int) (y : Int) (l : List Int)
    (h : y ∈ xs) :
    xorMerge xs (y :: l) = xorMerge (xs.erase y) l := by
  rw [xorMerge_cons, xorInsert_mem _ _ h]

/-- Membership-aware cons step: when `y ∉ xs`, peeling `y` prepends to xs. -/
theorem xorMerge_cons_not_mem (xs : List Int) (y : Int) (l : List Int)
    (h : y ∉ xs) :
    xorMerge xs (y :: l) = xorMerge (y :: xs) l := by
  rw [xorMerge_cons, xorInsert_not_mem _ _ h]


/-- `xorMerge` with a singleton is just one `xorInsert`. -/
theorem xorMerge_singleton (xs : List Int) (y : Int) :
    xorMerge xs [y] = xorInsert y xs := by
  simp [xorMerge]

/-- `xorMerge xs [y]` with `y ∉ xs`: the result is `y :: xs`. -/
theorem xorMerge_singleton_not_mem (xs : List Int) (y : Int) (h : y ∉ xs) :
    xorMerge xs [y] = y :: xs := by
  rw [xorMerge_singleton]
  exact xorInsert_not_mem y xs h

/-- `xorMerge xs [y]` with `y ∈ xs`: the result is `xs.erase y`. -/
theorem xorMerge_singleton_mem (xs : List Int) (y : Int) (h : y ∈ xs) :
    xorMerge xs [y] = xs.erase y := by
  rw [xorMerge_singleton]
  exact xorInsert_mem y xs h

/-- Length of `xorMerge xs [y]` when `y ∉ xs`: prepending adds 1. -/
theorem xorMerge_singleton_not_mem_length
    (xs : List Int) (y : Int) (h : y ∉ xs) :
    (xorMerge xs [y]).length = xs.length + 1 := by
  rw [xorMerge_singleton_not_mem _ _ h]
  simp

/-- Length of `xorMerge xs [y]` when `y ∈ xs`: erase removes one. -/
theorem xorMerge_singleton_mem_length
    (xs : List Int) (y : Int) (h_mem : y ∈ xs) :
    (xorMerge xs [y]).length = xs.length - 1 := by
  rw [xorMerge_singleton_mem _ _ h_mem]
  exact List.length_erase_of_mem h_mem

/-- `xorMerge` distributes over list append in the second argument. -/
theorem xorMerge_append (xs ys zs : List Int) :
    xorMerge xs (ys ++ zs) = xorMerge (xorMerge xs ys) zs := by
  unfold xorMerge
  rw [List.foldl_append]

/-- `xorMerge` preserves `Nodup` of the first (bag) argument: each
    `xorInsert` step preserves Nodup, so the fold does too. -/
theorem xorMerge_nodup (xs ys : List Int) (h : xs.Nodup) :
    (xorMerge xs ys).Nodup := by
  induction ys generalizing xs with
  | nil => exact h
  | cons y rest ih =>
    rw [xorMerge_cons]
    exact ih (xorInsert y xs) (xorInsert_nodup y xs h)

/-- **Symmetric-difference characterisation**: under `Nodup` of both
    arguments, `xorMerge xs ys` realises the symmetric difference
    `(xs \ ys) ∪ (ys \ xs)` at the membership level.  Induction on `ys`,
    using iter-221's toggle-membership lemmas at each step. -/
theorem xorMerge_mem_iff (xs ys : List Int)
    (h_xs : xs.Nodup) (h_ys : ys.Nodup) (x : Int) :
    x ∈ xorMerge xs ys ↔ (x ∈ xs ∧ x ∉ ys) ∨ (x ∉ xs ∧ x ∈ ys) := by
  induction ys generalizing xs with
  | nil => simp [xorMerge]
  | cons y rest ih =>
    rw [xorMerge_cons]
    obtain ⟨h_y_not_rest, h_rest_nodup⟩ := List.nodup_cons.mp h_ys
    have h_xy_nodup := xorInsert_nodup y xs h_xs
    rw [ih (xorInsert y xs) h_xy_nodup h_rest_nodup]
    by_cases h_eq : x = y
    · subst h_eq
      rw [xorInsert_mem_self_iff_nodup x xs h_xs]
      simp [h_y_not_rest]
    · rw [xorInsert_mem_other_iff y xs x h_eq]
      simp [List.mem_cons, h_eq]

/-- **`xorMerge` of a list with itself is empty** (under `Nodup`).
    Symmetric difference `xs △ xs = ∅`.  Direct corollary of
    `xorMerge_mem_iff` plus `List.eq_nil_iff_forall_not_mem`. -/
theorem xorMerge_self_eq_nil (xs : List Int) (h : xs.Nodup) :
    xorMerge xs xs = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x h_in
  rw [xorMerge_mem_iff xs xs h h] at h_in
  rcases h_in with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 h1
  · exact h1 h2

/-- **`xorMerge` head extraction (membership level)**: when `a ∉ ys` and
    `a ∉ l`, the head `a` survives the merge — `x ∈ xorMerge (a :: l) ys
    ↔ x ∈ a :: xorMerge l ys`.  Bridges `xorMerge` reasoning to head/tail
    decomposition for elements disjoint from the merging rule. -/
theorem xorMerge_cons_left_mem_iff (a : Int) (l ys : List Int)
    (h_a_ys : a ∉ ys) (h_l : l.Nodup) (h_a : a ∉ l) (h_ys : ys.Nodup) (x : Int) :
    x ∈ xorMerge (a :: l) ys ↔ x ∈ a :: xorMerge l ys := by
  have h_al : (a :: l).Nodup := List.nodup_cons.mpr ⟨h_a, h_l⟩
  rw [xorMerge_mem_iff (a :: l) ys h_al h_ys]
  rw [List.mem_cons]
  rw [List.mem_cons]
  rw [xorMerge_mem_iff l ys h_l h_ys]
  by_cases h_eq : x = a
  · subst h_eq; simp [h_a, h_a_ys]
  · simp [h_eq]

/-- **`xorMerge` reduces to union when disjoint**: if `xs ∩ ys = ∅`,
    `xorMerge xs ys` realises set union at the membership level.
    Direct corollary of iter 222's symmetric-difference characterisation. -/
theorem xorMerge_disjoint_mem_iff (xs ys : List Int)
    (h_xs : xs.Nodup) (h_ys : ys.Nodup) (h_disj : ∀ x ∈ xs, x ∉ ys) (x : Int) :
    x ∈ xorMerge xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  rw [xorMerge_mem_iff xs ys h_xs h_ys]
  by_cases h : x ∈ xs
  · simp [h, h_disj x h]
  · simp [h]

/-- **`xorMerge` empty-left membership**: `x ∈ xorMerge [] xs ↔ x ∈ xs`
    (under `xs.Nodup`).  Symmetric difference of `∅` and `xs` is `xs`. -/
theorem xorMerge_empty_left_mem_iff (xs : List Int)
    (h : xs.Nodup) (x : Int) :
    x ∈ xorMerge [] xs ↔ x ∈ xs := by
  rw [xorMerge_mem_iff [] xs List.nodup_nil h]
  simp

/-- **`xorMerge` is membership-commutative**: `x ∈ xorMerge xs ys ↔
    x ∈ xorMerge ys xs` (under Nodup hypotheses).  Symmetric difference
    is symmetric. -/
theorem xorMerge_mem_comm (xs ys : List Int)
    (h_xs : xs.Nodup) (h_ys : ys.Nodup) (x : Int) :
    x ∈ xorMerge xs ys ↔ x ∈ xorMerge ys xs := by
  rw [xorMerge_mem_iff xs ys h_xs h_ys, xorMerge_mem_iff ys xs h_ys h_xs]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩

/-- **Iter 969: membership-preservation in `xorMerge`**.  When `x ∈ xs`
    and `x ∉ ys` (with both `Nodup`), `x ∈ xorMerge xs ys`.  Direct
    consequence of the symmetric-difference characterisation:
    elements in only one side survive.  Useful for proving "the 1 in
    the bag is preserved across the System5 P-step xorMerge", a
    prerequisite for chaining 4 consecutive P-steps in the false-head
    case. -/
theorem xorMerge_mem_left_of_not_mem_right
    (xs ys : List Int) (h_xs : xs.Nodup) (h_ys : ys.Nodup)
    (x : Int) (h_in : x ∈ xs) (h_out : x ∉ ys) :
    x ∈ xorMerge xs ys := by
  rw [xorMerge_mem_iff xs ys h_xs h_ys]
  exact Or.inl ⟨h_in, h_out⟩

/-- An empty bag merged with a rule is the rule's xor-fold from `[]`. -/
theorem xorMerge_empty_left (ys : List Int) :
    xorMerge [] ys = ys.foldl (fun acc y => xorInsert y acc) [] := by
  simp [xorMerge]

/-- **Iter 912: disjoint xorMerge as list concat**.  When `xs` and `ys`
    are disjoint and `ys` has no duplicates that aren't already in xs,
    `xorMerge xs ys = ys.reverse ++ xs`.  Each xorInsert prepends its
    argument when it's absent, so foldl produces the reversed list
    prepended to the original. -/
theorem xorMerge_disjoint_eq_reverse_append (xs ys : List Int)
    (h_disjoint : ∀ y ∈ ys, y ∉ xs)
    (h_ys : ys.Nodup) :
    xorMerge xs ys = ys.reverse ++ xs := by
  induction ys generalizing xs with
  | nil => simp [xorMerge]
  | cons y rest ih =>
    rw [xorMerge_cons]
    obtain ⟨h_y_not_rest, h_rest_nodup⟩ := List.nodup_cons.mp h_ys
    have h_y_not_xs : y ∉ xs := h_disjoint y List.mem_cons_self
    rw [xorInsert_not_mem _ _ h_y_not_xs]
    have h_disjoint' : ∀ z ∈ rest, z ∉ (y :: xs) := by
      intro z hz_mem hz_in
      rcases List.mem_cons.mp hz_in with h_zy | h_zxs
      · subst h_zy; exact h_y_not_rest hz_mem
      · exact h_disjoint z (List.mem_cons.mpr (Or.inr hz_mem)) h_zxs
    rw [ih (y :: xs) h_disjoint' h_rest_nodup]
    simp

/-- **Iter 953: disjoint xorMerge length**.  Sum of lengths when
    disjoint and Nodup (corollary of iter 912's list form). -/
theorem xorMerge_disjoint_length (xs ys : List Int)
    (h_disjoint : ∀ y ∈ ys, y ∉ xs)
    (h_ys : ys.Nodup) :
    (xorMerge xs ys).length = xs.length + ys.length := by
  rw [xorMerge_disjoint_eq_reverse_append xs ys h_disjoint h_ys]
  simp [List.length_reverse]; omega

/-- **Iter 872 self-cancellation (membership level)**: merging the same
    rule twice is membership-equivalent to the original bag.  This
    captures the algebraic property `(xs △ r) △ r = xs` for symmetric
    difference, at the Nodup-membership level (the actual list might
    differ in order from `xs`).

    Used in the false-head System 5 trajectory analysis: the encoder
    pops r₁ at step 1 and a numerically-equal rule at step 2 (after
    intermediate bag decrement), and these xor-cancel back to the
    pre-pop bag minus the consumed false-bit prefix.  See iter 871
    trajectory trace in CTSToSystem5.lean. -/
theorem xorMerge_self_cancel_mem_iff (xs r : List Int)
    (h_xs : xs.Nodup) (h_r : r.Nodup) (x : Int) :
    x ∈ xorMerge (xorMerge xs r) r ↔ x ∈ xs := by
  have h_xy_nodup : (xorMerge xs r).Nodup := xorMerge_nodup xs r h_xs
  rw [xorMerge_mem_iff (xorMerge xs r) r h_xy_nodup h_r,
      xorMerge_mem_iff xs r h_xs h_r]
  by_cases h_in_xs : x ∈ xs <;> by_cases h_in_r : x ∈ r <;>
    simp [h_in_xs, h_in_r]

/-- **Iter 999: xorMerge of same-membership lists has no elements**.
    When `ys` and `zs` are both `Nodup` and have the same membership
    set, `xorMerge ys zs` is empty (at the membership level).  Used in
    the bag-2 cancellation: r1.reverse and r2.map(·+2) have the same
    membership (since r1 = r2.map(·+2) by encoder identity, iter 888),
    so xorMerge cancels them to nothing. -/
theorem xorMerge_same_mem_no_mem (ys zs : List Int)
    (h_ys : ys.Nodup) (h_zs : zs.Nodup)
    (h_mem : ∀ x, x ∈ ys ↔ x ∈ zs) (x : Int) :
    x ∉ xorMerge ys zs := by
  rw [xorMerge_mem_iff ys zs h_ys h_zs]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact h2 ((h_mem x).mp h1)
  · exact h1 ((h_mem x).mpr h2)

end BiTM
