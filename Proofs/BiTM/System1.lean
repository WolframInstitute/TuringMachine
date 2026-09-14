/-
  BiTM.System1

  Smith's "System 1" (PDF `TM23Proof.pdf` p. 4): a generalised TM
  on a 6-symbol alphabet (3 base symbols 0/1/2 + 3 compound symbols
  20/21/22) that emulates wolfram23 with shortcuts via multi-cell
  writes.  Equivalent to wolfram23 on valid configs.

  Extracted from `BiTM.CockeMinskyConstruction` in a refactor.

  Contents:
    * `System1Symbol` inductive
    * `system1` — System 1's transition table
    * `natToSystem1Symbol`, `wolfram23CfgToSystem1` — encoders
    * `wolfram23_step_eq_system1_step` — single-step equivalence
    * `wolfram23_nSteps_eq_system1_nSteps` — multi-step equivalence
    * `wolfram23_halts_iff_system1_halts` — halt equivalence
-/

import BiTM.Basic
import BiTM.HaltInduction
import BiTM.Wolfram23Valid
import BiTM.GeneralizedTM

namespace BiTM

open TM

/-- **SCAFFOLD** for System 1 (PDF p. 4).  Adds 3 new transitions on top
    of System 0: (B, 20), (B, 21), (B, 22) → multi-cell writes.

    The multi-cell-write semantics are now expressible via `GeneralizedTM`,
    but the actual transition table still needs to be filled in from
    PDF p. 4's visual diagram. -/
inductive System1Symbol : Type
  /-- Standard symbols 0, 1, 2 (= System 0 alphabet). -/
  | base : Fin 3 → System1Symbol
  /-- Extra symbols 20, 21, 22 (compound values from System 1's
      multi-cell-write semantics). -/
  | compound : Fin 3 → System1Symbol
  deriving DecidableEq, Repr

/-- System 1's transition table.  Matches System 0 on `base` symbols (the
    standard wolfram23 transitions, lifted to `System1Symbol`).
    Compound symbols 20, 21, 22 in state B trigger Smith's "shortcut"
    multi-cell writes per PDF p. 4.

    SORRY[system1-compound-transitions]: the (B, 20)/(B, 21)/(B, 22)
    transitions need careful reading of the PDF's visual (their `dir`
    values aren't unambiguous from the text I have access to). -/
def system1 : GeneralizedTM System1Symbol where
  numStates := 3  -- 0 = halt, 1 = A, 2 = B
  transition := fun state sym =>
    match state, sym with
    -- System 0 transitions on base symbols, lifted to System1Symbol.
    -- A = state 1.
    | 1, System1Symbol.base ⟨0, _⟩ =>
        { nextState := 2, writes := [System1Symbol.base ⟨1, by omega⟩], dir := Dir.R }
    | 1, System1Symbol.base ⟨1, _⟩ =>
        { nextState := 1, writes := [System1Symbol.base ⟨2, by omega⟩], dir := Dir.L }
    | 1, System1Symbol.base ⟨2, _⟩ =>
        { nextState := 1, writes := [System1Symbol.base ⟨1, by omega⟩], dir := Dir.L }
    -- B = state 2.
    | 2, System1Symbol.base ⟨0, _⟩ =>
        { nextState := 1, writes := [System1Symbol.base ⟨2, by omega⟩], dir := Dir.L }
    | 2, System1Symbol.base ⟨1, _⟩ =>
        { nextState := 2, writes := [System1Symbol.base ⟨2, by omega⟩], dir := Dir.R }
    | 2, System1Symbol.base ⟨2, _⟩ =>
        { nextState := 1, writes := [System1Symbol.base ⟨0, by omega⟩], dir := Dir.R }
    -- Compound transitions in state B (Smith's shortcuts).
    -- The actual writes/dir need PDF visual; placeholder = halt.
    | 2, System1Symbol.compound _ =>
        { nextState := 0, writes := [], dir := Dir.R }
    -- All other (state, symbol) combinations halt.
    | _, _ =>
        { nextState := 0, writes := [], dir := Dir.R }

/-- Translate a `Nat` symbol (wolfram23's alphabet) to a `System1Symbol`.
    Values 0/1/2 → `base`; values 20/21/22 → `compound`; otherwise
    fallback to `base 0` (shouldn't occur on valid wolfram23 cfgs). -/
def natToSystem1Symbol (n : Nat) : System1Symbol :=
  if h : n < 3 then System1Symbol.base ⟨n, h⟩
  else if h_lo : 20 ≤ n then
    if h_hi : n - 20 < 3 then
      System1Symbol.compound ⟨n - 20, h_hi⟩
    else System1Symbol.base ⟨0, by decide⟩
  else System1Symbol.base ⟨0, by decide⟩

/-- Translate a `BiTM.Config` (wolfram23 cfg) to a `GenConfig System1Symbol`. -/
def wolfram23CfgToSystem1 (cfg : Config) : GenConfig System1Symbol :=
  { state := cfg.state
    left := cfg.left.map natToSystem1Symbol
    head := natToSystem1Symbol cfg.head
    right := cfg.right.map natToSystem1Symbol }

/-- Sanity check: translating wolfram23_init gives the corresponding
    System 1 config with state 1, blank head, empty tape. -/
example : wolfram23CfgToSystem1 wolfram23_init
    = { state := 1, left := [], head := System1Symbol.base ⟨0, by decide⟩,
        right := [] : GenConfig System1Symbol } := by
  decide

/-- **First-step equivalence (concrete)**: one `wolfram23.step` from
    `wolfram23_init` matches one `system1.step` on the translated cfg.

    This is a single-case sanity check toward the full
    `wolfram23_step_eq_system1_step` lemma (which would generalize over
    all valid configs). -/
example :
    (step wolfram23 wolfram23_init).map wolfram23CfgToSystem1
    = GeneralizedTM.step (System1Symbol.base ⟨0, by decide⟩) system1
        (wolfram23CfgToSystem1 wolfram23_init) := by
  decide

/-- **Step equivalence on empty-tape configs**: for the 6 valid
    `(state, head)` pairs with `left = right = []`, wolfram23 step
    matches system1 step on the translated cfg.  All 6 cases discharged
    by `decide` (since the configs are fully concrete). -/
example :
    ∀ (state : Fin 2) (head : Fin 3),
      (step wolfram23 { state := state.val + 1, left := [],
                         head := head.val, right := [] }).map
        wolfram23CfgToSystem1
      = GeneralizedTM.step (System1Symbol.base ⟨0, by decide⟩) system1
          (wolfram23CfgToSystem1
             { state := state.val + 1, left := [],
               head := head.val, right := [] }) := by
  decide

/-- **Step equivalence on single-element-tape configs**: extends iter 176
    to configs with `left = [l.val]`, `right = [r.val]` for any
    `l, r ∈ {0, 1, 2}`.  All 2 × 3 × 3 × 3 = 54 cases via `decide`. -/
example :
    ∀ (state : Fin 2) (head l r : Fin 3),
      (step wolfram23 { state := state.val + 1, left := [l.val],
                         head := head.val, right := [r.val] }).map
        wolfram23CfgToSystem1
      = GeneralizedTM.step (System1Symbol.base ⟨0, by decide⟩) system1
          (wolfram23CfgToSystem1
             { state := state.val + 1, left := [l.val],
               head := head.val, right := [r.val] }) := by
  decide

/-- For `n < 3`, `natToSystem1Symbol n = base ⟨n, _⟩`. -/
theorem natToSystem1Symbol_lt_3 (n : Nat) (h : n < 3) :
    natToSystem1Symbol n = System1Symbol.base ⟨n, h⟩ := by
  unfold natToSystem1Symbol
  rw [dif_pos h]

/-- For valid wolfram23 cfgs, the head's translation is `base ⟨head, _⟩`. -/
theorem wolfram23CfgToSystem1_head_valid (cfg : Config) (h : IsValidWolfram23Cfg cfg) :
    (wolfram23CfgToSystem1 cfg).head
      = System1Symbol.base ⟨cfg.head, h.2.1⟩ := by
  unfold wolfram23CfgToSystem1
  exact natToSystem1Symbol_lt_3 cfg.head h.2.1

/-- **General step equivalence**: for any valid wolfram23 cfg,
    `wolfram23.step` matches `system1.step` on the translation.

    Proof: explicit case analysis on `(state, head)` (6 cases),
    then on read-side (`[]` vs `h :: t`) for each.  In each case,
    `simp` with all relevant definitions closes the equality. -/
theorem wolfram23_step_eq_system1_step (cfg : Config) (h_valid : IsValidWolfram23Cfg cfg) :
    (step wolfram23 cfg).map wolfram23CfgToSystem1
    = GeneralizedTM.step (System1Symbol.base ⟨0, by decide⟩) system1
        (wolfram23CfgToSystem1 cfg) := by
  rcases h_valid with ⟨h_state, h_head, h_left, h_right⟩
  have h_h0 : cfg.head = 0 ∨ cfg.head = 1 ∨ cfg.head = 2 := by omega
  rcases h_state with h_s | h_s
  -- ===== state = 1 =====
  · rcases h_h0 with h_h | h_h | h_h
    · cases h_r : cfg.right with
      | nil =>
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_r]
      | cons head tail =>
          have h_lt : head < 3 := h_right head (by simp [h_r])
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_r, dif_pos h_lt]
    · cases h_l : cfg.left with
      | nil =>
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_l]
      | cons head tail =>
          have h_lt : head < 3 := h_left head (by simp [h_l])
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_l, dif_pos h_lt]
    · cases h_l : cfg.left with
      | nil =>
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_l]
      | cons head tail =>
          have h_lt : head < 3 := h_left head (by simp [h_l])
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_l, dif_pos h_lt]
  -- ===== state = 2 =====
  · rcases h_h0 with h_h | h_h | h_h
    · cases h_l : cfg.left with
      | nil =>
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_l]
      | cons head tail =>
          have h_lt : head < 3 := h_left head (by simp [h_l])
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_l, dif_pos h_lt]
    · cases h_r : cfg.right with
      | nil =>
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_r]
      | cons head tail =>
          have h_lt : head < 3 := h_right head (by simp [h_r])
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_r, dif_pos h_lt]
    · cases h_r : cfg.right with
      | nil =>
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_r]
      | cons head tail =>
          have h_lt : head < 3 := h_right head (by simp [h_r])
          simp [step, GeneralizedTM.step, system1, wolfram23,
                wolfram23CfgToSystem1, natToSystem1Symbol, readHead,
                h_s, h_h, h_r, dif_pos h_lt]

/-- Helper: `GeneralizedTM.nSteps blank tm cfg (n+1)` unfolds to the match. -/
private theorem GeneralizedTM.nSteps_succ_unfold {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg : GenConfig Sym) (n : Nat) :
    GeneralizedTM.nSteps blank tm cfg (n + 1)
    = match GeneralizedTM.step blank tm cfg with
      | none => none
      | some cfg' => GeneralizedTM.nSteps blank tm cfg' n := rfl

/-- **Multi-step equivalence**: for any valid wolfram23 cfg and any n,
    `nSteps` in wolfram23 matches `nSteps` in system1 (modulo translation).

    Proof: induction on n using iter-182's single-step equivalence
    and `step_wolfram23_preserves_valid`. -/
theorem wolfram23_nSteps_eq_system1_nSteps (cfg : Config) (n : Nat)
    (h_valid : IsValidWolfram23Cfg cfg) :
    (nSteps wolfram23 cfg n).map wolfram23CfgToSystem1
    = GeneralizedTM.nSteps (System1Symbol.base ⟨0, by decide⟩) system1
        (wolfram23CfgToSystem1 cfg) n := by
  induction n generalizing cfg with
  | zero => simp [nSteps, GeneralizedTM.nSteps]
  | succ n ih =>
    have h_step_eq := wolfram23_step_eq_system1_step cfg h_valid
    obtain ⟨cfg', h_step_some, h_valid'⟩ := step_wolfram23_preserves_valid cfg h_valid
    have h_step_eq' :
        GeneralizedTM.step (System1Symbol.base ⟨0, by decide⟩) system1
            (wolfram23CfgToSystem1 cfg) = some (wolfram23CfgToSystem1 cfg') := by
      rw [← h_step_eq, h_step_some, Option.map_some]
    rw [BiTM_nSteps_succ_unfold, GeneralizedTM.nSteps_succ_unfold,
        h_step_some, h_step_eq']
    exact ih cfg' h_valid'

/-- **Halt-step equivalence**: for valid wolfram23 cfgs, `nSteps`-halting
    in wolfram23 at step n is equivalent to `nSteps`-halting in System 1
    at the same step.  Direct corollary of
    `wolfram23_nSteps_eq_system1_nSteps` via `Option.map_eq_none_iff`. -/
theorem wolfram23_nSteps_none_iff_system1_nSteps_none
    (cfg : Config) (n : Nat) (h_valid : IsValidWolfram23Cfg cfg) :
    nSteps wolfram23 cfg n = none
    ↔ GeneralizedTM.nSteps (System1Symbol.base ⟨0, by decide⟩) system1
          (wolfram23CfgToSystem1 cfg) n = none := by
  have h := wolfram23_nSteps_eq_system1_nSteps cfg n h_valid
  rw [← h, Option.map_eq_none_iff]

/-- **Halts-equivalence**: for valid wolfram23 cfgs, "halts via nSteps in
    wolfram23" iff "halts in System 1 (modulo translation)".  Existential
    closure of `wolfram23_nSteps_none_iff_system1_nSteps_none`. -/
theorem wolfram23_halts_iff_system1_halts
    (cfg : Config) (h_valid : IsValidWolfram23Cfg cfg) :
    (∃ n, nSteps wolfram23 cfg n = none)
    ↔ GeneralizedTM.Halts (System1Symbol.base ⟨0, by decide⟩) system1
          (wolfram23CfgToSystem1 cfg) := by
  unfold GeneralizedTM.Halts
  exact ⟨fun ⟨n, h⟩ =>
            ⟨n, (wolfram23_nSteps_none_iff_system1_nSteps_none cfg n h_valid).mp h⟩,
         fun ⟨n, h⟩ =>
            ⟨n, (wolfram23_nSteps_none_iff_system1_nSteps_none cfg n h_valid).mpr h⟩⟩


/-- **System 1 halts ⟹ wolfram23 halts** (on valid cfgs).  Composes
    `wolfram23_halts_iff_system1_halts` (iter 186) with
    `nSteps_none_imp_halts` (iter 187): if the System 1 translation
    of a valid wolfram23 cfg halts, the original cfg also halts in
    the eval-style `BiTM.Halts` predicate that `smith_reduces` consumes. -/
theorem system1_halts_imp_wolfram23_halts
    (cfg : Config) (h_valid : IsValidWolfram23Cfg cfg)
    (h : GeneralizedTM.Halts (System1Symbol.base ⟨0, by decide⟩) system1
            (wolfram23CfgToSystem1 cfg)) :
    Halts wolfram23 cfg :=
  nSteps_none_imp_halts wolfram23 cfg
    ((wolfram23_halts_iff_system1_halts cfg h_valid).mpr h)

/-- **`wolfram23_halts_imp_system1_halts` (iter 616)**: forward
    direction — wolfram23 `Halts` (eval-form) ⟹ System 1 `Halts` on the
    translation.  Composes `halts_imp_nSteps_none` (eval-Halts to ∃n
    nSteps=none) with the forward iff at the nSteps level. -/
theorem wolfram23_halts_imp_system1_halts
    (cfg : Config) (h_valid : IsValidWolfram23Cfg cfg)
    (h : Halts wolfram23 cfg) :
    GeneralizedTM.Halts (System1Symbol.base ⟨0, by decide⟩) system1
        (wolfram23CfgToSystem1 cfg) :=
  (wolfram23_halts_iff_system1_halts cfg h_valid).mp
    (halts_imp_nSteps_none wolfram23 cfg h)

/-- **`wolfram23CfgToSystem1_state` (iter 616)**: the encoder
    preserves `state` exactly.  Direct unfold. -/
@[simp] theorem wolfram23CfgToSystem1_state (cfg : Config) :
    (wolfram23CfgToSystem1 cfg).state = cfg.state := rfl

/-- **`wolfram23CfgToSystem1_left_length` (iter 616)**: the encoder
    preserves `left.length`.  Direct via `List.length_map`. -/
@[simp] theorem wolfram23CfgToSystem1_left_length (cfg : Config) :
    (wolfram23CfgToSystem1 cfg).left.length = cfg.left.length := by
  unfold wolfram23CfgToSystem1
  exact List.length_map _

/-- **`wolfram23CfgToSystem1_right_length` (iter 616)**: the encoder
    preserves `right.length`. -/
@[simp] theorem wolfram23CfgToSystem1_right_length (cfg : Config) :
    (wolfram23CfgToSystem1 cfg).right.length = cfg.right.length := by
  unfold wolfram23CfgToSystem1
  exact List.length_map _

/-- Inverse of `natToSystem1Symbol` on the System 1 alphabet.  Round-trips
    only on `n ∈ {0, 1, 2, 20, 21, 22}` (where the forward map doesn't
    fall back to `base 0`). -/
def system1SymbolToNat (s : System1Symbol) : Nat :=
  match s with
  | System1Symbol.base ⟨n, _⟩ => n
  | System1Symbol.compound ⟨n, _⟩ => 20 + n

/-- Symbol-level round trip on the wolfram23 alphabet (`n < 3`). -/
theorem system1SymbolToNat_natToSystem1Symbol_of_lt_3 (n : Nat) (h : n < 3) :
    system1SymbolToNat (natToSystem1Symbol n) = n := by
  unfold natToSystem1Symbol
  rw [dif_pos h]; rfl

/-- Inverse of `wolfram23CfgToSystem1`.  Decodes each symbol back to its
    `Nat` value via `system1SymbolToNat`. -/
def system1CfgToWolfram23 (cfg : GenConfig System1Symbol) : Config :=
  { state := cfg.state
    left := cfg.left.map system1SymbolToNat
    head := system1SymbolToNat cfg.head
    right := cfg.right.map system1SymbolToNat }

/-- Helper: list round trip on Nat lists with all entries `< 3`. -/
private theorem list_natToS1_round_trip (l : List Nat) (h : ∀ x ∈ l, x < 3) :
    (l.map natToSystem1Symbol).map system1SymbolToNat = l := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    show system1SymbolToNat (natToSystem1Symbol head)
         :: (tail.map natToSystem1Symbol).map system1SymbolToNat = head :: tail
    rw [system1SymbolToNat_natToSystem1Symbol_of_lt_3 head
          (h head (List.mem_cons.mpr (Or.inl rfl))),
        ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

/-- **Cfg-level round trip**: `system1CfgToWolfram23 ∘ wolfram23CfgToSystem1
    = id` on valid wolfram23 cfgs.  This makes
    `wolfram23CfgToSystem1` injective on valid cfgs. -/
theorem system1CfgToWolfram23_wolfram23CfgToSystem1
    (cfg : Config) (h : IsValidWolfram23Cfg cfg) :
    system1CfgToWolfram23 (wolfram23CfgToSystem1 cfg) = cfg := by
  obtain ⟨_, h_head, h_left, h_right⟩ := h
  show ({ state := cfg.state
          left := (cfg.left.map natToSystem1Symbol).map system1SymbolToNat
          head := system1SymbolToNat (natToSystem1Symbol cfg.head)
          right := (cfg.right.map natToSystem1Symbol).map system1SymbolToNat } : Config)
       = cfg
  rw [list_natToS1_round_trip cfg.left h_left,
      system1SymbolToNat_natToSystem1Symbol_of_lt_3 cfg.head h_head,
      list_natToS1_round_trip cfg.right h_right]

/-- Direct injectivity of `wolfram23CfgToSystem1` on valid cfgs. -/
theorem wolfram23CfgToSystem1_injective_on_valid
    (cfg₁ cfg₂ : Config)
    (h₁ : IsValidWolfram23Cfg cfg₁) (h₂ : IsValidWolfram23Cfg cfg₂)
    (h_eq : wolfram23CfgToSystem1 cfg₁ = wolfram23CfgToSystem1 cfg₂) :
    cfg₁ = cfg₂ := by
  have h_rt₁ := system1CfgToWolfram23_wolfram23CfgToSystem1 cfg₁ h₁
  have h_rt₂ := system1CfgToWolfram23_wolfram23CfgToSystem1 cfg₂ h₂
  rw [← h_rt₁, ← h_rt₂, h_eq]

/-- **Existential form of iter 182**: System 1's step on a valid translated
    cfg lands in the all-base subspace (i.e., is itself the translation
    of a valid wolfram23 cfg).  Combines iter 182 with
    `step_wolfram23_preserves_valid`. -/
theorem system1_step_preserves_translation
    (cfg : Config) (h_valid : IsValidWolfram23Cfg cfg) :
    ∃ cfg', GeneralizedTM.step (System1Symbol.base ⟨0, by decide⟩) system1
              (wolfram23CfgToSystem1 cfg) = some (wolfram23CfgToSystem1 cfg')
            ∧ IsValidWolfram23Cfg cfg' := by
  obtain ⟨cfg', h_step, h_valid'⟩ := step_wolfram23_preserves_valid cfg h_valid
  refine ⟨cfg', ?_, h_valid'⟩
  rw [← wolfram23_step_eq_system1_step cfg h_valid, h_step, Option.map_some]

/-- **System 1 trajectory from `wolfram23_init`**: instantiation of iter
    184 to the standard initial cfg.  Combines
    `wolfram23_nSteps_eq_system1_nSteps` with the existing
    `wolfram23_at_n_eq_nSteps` ground-truth trajectory definition. -/
theorem system1_nSteps_init_eq_translated_at_n (n : Nat) :
    GeneralizedTM.nSteps (System1Symbol.base ⟨0, by decide⟩) system1
        (wolfram23CfgToSystem1 wolfram23_init) n
    = some (wolfram23CfgToSystem1 (wolfram23_at_n n)) := by
  have h := wolfram23_nSteps_eq_system1_nSteps wolfram23_init n wolfram23_init_valid
  rw [wolfram23_at_n_eq_nSteps n] at h
  simpa using h.symm

/-- **Contrapositive of iter 188**: System 1's translation of a valid
    wolfram23 cfg does **not** halt.  Combines `system1_halts_imp_wolfram23_halts`
    (iter 188) with `not_halts_wolfram23_valid` (the fact that wolfram23
    never reaches state 0 from any cfg with state ∈ {1, 2}).

    PREDICATE-WEAKNESS NOTE: this exposes that the `nSteps`-form
    chain `CTS halts → ... → wolfram23 halts` is *vacuously* satisfied
    on valid cfgs — wolfram23 simply never halts from them, so the only
    way `smith_reduces` (`Halts wolfram23 (encode cfg)`) is non-trivially
    satisfiable is for the encoder to produce **invalid** wolfram23 cfgs
    (e.g. the trivial halt-collapse to state 0).  A meaningful faithful
    Smith predicate would replace `Halts wolfram23` with a tape-pattern
    recognition criterion. -/
theorem system1_not_halts_on_valid_translation (cfg : Config)
    (h_valid : IsValidWolfram23Cfg cfg) :
    ¬ GeneralizedTM.Halts (System1Symbol.base ⟨0, by decide⟩) system1
        (wolfram23CfgToSystem1 cfg) := by
  intro h_halts
  exact not_halts_wolfram23_valid cfg h_valid
    (system1_halts_imp_wolfram23_halts cfg h_valid h_halts)

/-- **`system1CfgToWolfram23_preserves_state` (iter 744)**: the
    inverse encoder preserves the state field directly (no decoding
    needed for the state, since System 1 cfgs share the same state
    field as wolfram23 cfgs).  Direct from the definition of
    `system1CfgToWolfram23`. -/
theorem system1CfgToWolfram23_preserves_state (cfg : GenConfig System1Symbol) :
    (system1CfgToWolfram23 cfg).state = cfg.state := rfl


end BiTM
