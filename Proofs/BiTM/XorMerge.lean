/-
  BiTM.XorMerge

  Symmetric-difference (parity-mod-2) list-bag operations used by the
  System 5 reduction in `BiTM.CockeMinskyConstruction`.

  Pure list utilities - no dependency on TM/Tag/CTS machinery.

  Contents:
    * `xorInsert`, `xorMerge` definitions
    * Membership / Nodup lemmas
    * Symmetric-difference characterisation (`xorMerge_mem_iff`)
-/

namespace BiTM

/-! ## Nodup transport along injective maps -/

/-- `List.map` preserves `Nodup` along an injective function. -/
theorem nodup_map_of_injective {alpha beta : Type} (f : alpha -> beta)
    (hf : forall a b : alpha, f a = f b -> a = b)
    {l : List alpha} (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    obtain ⟨h_a, h_t⟩ := List.nodup_cons.mp h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h_t⟩
    intro h_mem
    obtain ⟨b, h_b, h_fb⟩ := List.mem_map.mp h_mem
    exact h_a ((hf b a h_fb) ▸ h_b)

/-- Decrementing every entry of an integer list preserves `Nodup`. -/
theorem nodup_map_sub_one {l : List Int} (h : l.Nodup) :
    (l.map (· - 1)).Nodup :=
  nodup_map_of_injective _ (fun a b hab => by omega) h

/-- Incrementing every entry of an integer list preserves `Nodup`. -/
theorem nodup_map_add_one {l : List Int} (h : l.Nodup) :
    (l.map (· + 1)).Nodup :=
  nodup_map_of_injective _ (fun a b hab => by omega) h

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

/-- `xorInsert x xs` prepends `x` when `x` is not in `xs`. -/
theorem xorInsert_not_mem (x : Int) (xs : List Int) (h : x ∉ xs) :
    xorInsert x xs = x :: xs := by
  unfold xorInsert
  rw [ite_eq_right h]

/-- `xorInsert x xs` erases `x` when `x` is in `xs`. -/
theorem xorInsert_mem (x : Int) (xs : List Int) (h : x ∈ xs) :
    xorInsert x xs = xs.erase x := by
  unfold xorInsert
  rw [ite_eq_left h]

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
    `y in xorInsert y xs <-> y not in xs`. -/
theorem xorInsert_mem_self_iff_nodup (y : Int) (xs : List Int) (h : xs.Nodup) :
    y ∈ xorInsert y xs ↔ y ∉ xs := by
  by_cases h_mem : y ∈ xs
  · rw [xorInsert_mem _ _ h_mem]
    constructor
    · intro h_in; exact absurd h_in (List.Nodup.not_mem_erase h)
    · intro h_not; exact absurd h_mem h_not
  · rw [xorInsert_not_mem _ _ h_mem]
    simp [h_mem]

/-- `xorInsert y` only affects membership of `y`: for any `x <> y`,
    `x in xorInsert y xs <-> x in xs`. -/
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
    `(xs \ ys) union (ys \ xs)` at the membership level.  Proved by
    induction on `ys` with the toggle-membership lemmas at each step. -/
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

/-- **Disjoint xorMerge as list concat**.  When `xs` and `ys`
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

/-- Every member of a `xorMerge` comes from one of the two arguments. -/
theorem xorMerge_mem_or (xs ys : List Int) (x : Int)
    (h : x ∈ xorMerge xs ys) : x ∈ xs ∨ x ∈ ys := by
  induction ys generalizing xs with
  | nil => left; simpa using h
  | cons y rest ih =>
    rw [xorMerge_cons] at h
    rcases ih (xorInsert y xs) h with h1 | h2
    · by_cases h_xy : x = y
      · right; rw [h_xy]; exact List.mem_cons_self
      · left; exact (xorInsert_mem_other_iff y xs x h_xy).mp h1
    · right; exact List.mem_cons.mpr (Or.inr h2)

end BiTM
