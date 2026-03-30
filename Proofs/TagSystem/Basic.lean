/-
  TagSystem.Basic

  Formalization of 2-tag systems and cyclic tag systems.
  These are intermediate computational models in universality proofs:
    Turing Machine → 2-Tag System → Cyclic Tag System → (Rule 110 / (2,3) TM)

  Canonical home: TuringMachineSearch/Proofs/TagSystem/
  Imported by both Rule110 and BiTM universality proofs.
-/

namespace TagSystem

-- ============================================================================
-- 2-Tag Systems
-- ============================================================================

/-- A 2-tag system over a finite alphabet of size k.
    Each step: read the first symbol, delete the first 2 symbols,
    append the production for the read symbol. -/
structure Tag (k : Nat) where
  /-- Production rules: for each symbol i ∈ Fin k, the string to append -/
  productions : Fin k → List (Fin k)

/-- Configuration of a tag system: just the current data word -/
abbrev TagConfig (k : Nat) := List (Fin k)

/-- A tag system halts when the data word has fewer than 2 symbols -/
def tagHalted {k : Nat} (cfg : TagConfig k) : Bool :=
  cfg.length < 2

/-- Single step of a 2-tag system.
    Returns none if halted (word too short). -/
def Tag.step {k : Nat} (ts : Tag k) (cfg : TagConfig k) : Option (TagConfig k) :=
  match cfg with
  | [] => none
  | [_] => none
  | a :: _ :: rest => some (rest ++ ts.productions a)

/-- Run a tag system for up to `fuel` steps.
    Returns the final configuration if halted, none if fuel exhausted. -/
def Tag.eval {k : Nat} (ts : Tag k) (cfg : TagConfig k) : Nat → Option (TagConfig k)
  | 0 => if tagHalted cfg then some cfg else none
  | fuel + 1 =>
    if tagHalted cfg then some cfg
    else match ts.step cfg with
      | none => some cfg  -- halted
      | some cfg' => ts.eval cfg' fuel

/-- A tag system halts on input cfg if eval returns some for some fuel -/
def Tag.Halts {k : Nat} (ts : Tag k) (cfg : TagConfig k) : Prop :=
  ∃ fuel result, ts.eval cfg fuel = some result

-- ============================================================================
-- Basic lemmas for Tag
-- ============================================================================

theorem Tag.eval_step {k : Nat} (ts : Tag k) (cfg cfg' : TagConfig k) (fuel : Nat)
    (hnh : tagHalted cfg = false) (hs : ts.step cfg = some cfg') :
    ts.eval cfg (fuel + 1) = ts.eval cfg' fuel := by
  simp [eval, hnh, hs]

theorem Tag.eval_halted {k : Nat} (ts : Tag k) (cfg : TagConfig k) (fuel : Nat)
    (hh : tagHalted cfg = true) :
    ts.eval cfg fuel = some cfg := by
  cases fuel with
  | zero => simp [eval, hh]
  | succ n => simp [eval, hh]

theorem Tag.step_none_iff_halted {k : Nat} (ts : Tag k) (cfg : TagConfig k) :
  ts.step cfg = none ↔ tagHalted cfg = true := by
  dsimp [Tag.step, tagHalted]
  cases cfg with
  | nil => simp
  | cons head tail =>
    cases tail with
    | nil => simp
    | cons head' tail' =>
      simp

theorem Tag.eval_add {k : Nat} (ts : Tag k) (n m : Nat) (cfg mid result : TagConfig k) :
  ts.eval cfg n = some mid → ts.eval mid m = some result → ts.eval cfg (n + m) = some result := by
  induction n generalizing cfg with
  | zero =>
    dsimp [Tag.eval]
    split
    · intro h1 h2
      injection h1 with e; subst e
      exact (by rw [Nat.zero_add]; exact h2)
    · intro h1
      contradiction
  | succ n ih =>
    dsimp [Tag.eval]
    split
    · rename_i h_halt
      intro h1 h2
      injection h1 with e; subst e
      have h3 := Tag.eval_halted ts cfg (n + 1 + m) h_halt
      have h4 := Tag.eval_halted ts cfg m h_halt
      rw [h4] at h2
      injection h2 with e; subst e
      exact h3
    · rename_i h_not_halt
      intro h1 h2
      cases h_step : ts.step cfg with
      | none =>
        have h_halt2 : tagHalted cfg = true := (Tag.step_none_iff_halted ts cfg).mp h_step
        rw [h_halt2] at h_not_halt
        contradiction
      | some cfg' =>
        rw [h_step] at h1
        have hm := ih cfg' h1 h2
        rw [Nat.add_right_comm]
        have h_halt_f : tagHalted cfg = false := by cases h_t : tagHalted cfg <;> simp_all
        rw [Tag.eval_step ts cfg cfg' (n + m) h_halt_f h_step]
        exact hm

-- ============================================================================
-- Cyclic Tag Systems
-- ============================================================================

/-- A cyclic tag system: binary alphabet, cyclic list of appendants.
    Each step:
    1. If the first bit is true, append the current appendant
    2. Delete the first bit
    3. Advance to the next appendant (cycling) -/
structure CTS where
  /-- The cyclic list of appendants (binary strings) -/
  appendants : List (List Bool)
  /-- Non-empty appendant list (needed for cycling) -/
  nonempty : appendants.length > 0

/-- Configuration of a CTS: data word + current phase -/
structure CTSConfig where
  /-- Current data word (binary) -/
  data : List Bool
  /-- Current phase: index into the appendant list (mod length) -/
  phase : Nat
  deriving DecidableEq, BEq, Repr

/-- A CTS halts when the data word is empty -/
def ctsHalted (cfg : CTSConfig) : Bool :=
  cfg.data.isEmpty

/-- Get the current appendant for a given phase -/
def CTS.currentAppendant (cts : CTS) (phase : Nat) : List Bool :=
  cts.appendants.get ⟨phase % cts.appendants.length, Nat.mod_lt _ cts.nonempty⟩

/-- Single step of a CTS.
    Returns none if data word is empty (halted). -/
def CTS.step (cts : CTS) (cfg : CTSConfig) : Option CTSConfig :=
  match cfg.data with
  | [] => none
  | head :: rest =>
    let newData := if head then rest ++ cts.currentAppendant cfg.phase else rest
    some { data := newData, phase := (cfg.phase + 1) % cts.appendants.length }

/-- Run a CTS for up to `fuel` steps. -/
def CTS.eval (cts : CTS) (cfg : CTSConfig) : Nat → Option CTSConfig
  | 0 => if ctsHalted cfg then some cfg else none
  | fuel + 1 =>
    if ctsHalted cfg then some cfg
    else match cts.step cfg with
      | none => some cfg
      | some cfg' => cts.eval cfg' fuel

/-- A CTS halts on input cfg if eval returns some for some fuel -/
def CTS.Halts (cts : CTS) (cfg : CTSConfig) : Prop :=
  ∃ fuel result, cts.eval cfg fuel = some result

/-- Run CTS for exactly n steps -/
def CTS.nSteps (cts : CTS) (cfg : CTSConfig) : Nat → Option CTSConfig
  | 0 => some cfg
  | n + 1 =>
    match cts.step cfg with
    | none => none
    | some cfg' => cts.nSteps cfg' n

-- ============================================================================
-- Basic lemmas
-- ============================================================================

theorem CTS.eval_step (cts : CTS) (cfg cfg' : CTSConfig) (fuel : Nat)
    (hnh : ctsHalted cfg = false) (hs : cts.step cfg = some cfg') :
    cts.eval cfg (fuel + 1) = cts.eval cfg' fuel := by
  simp [eval, hnh, hs]

theorem CTS.eval_halted (cts : CTS) (cfg : CTSConfig) (fuel : Nat)
    (hh : ctsHalted cfg = true) :
    cts.eval cfg fuel = some cfg := by
  cases fuel with
  | zero => simp [eval, hh]
  | succ n => simp [eval, hh]

-- ============================================================================
-- Examples
-- ============================================================================

/-- A simple 1-appendant CTS for testing -/
def exampleCTS : CTS where
  appendants := [[true]]
  nonempty := by simp

def exampleCTSInit : CTSConfig :=
  { data := [false, true], phase := 0 }

theorem example_cts_step1 :
    exampleCTS.step exampleCTSInit = some { data := [true], phase := 0 } := by
  native_decide

theorem example_cts_step2 :
    (do let s1 ← exampleCTS.step exampleCTSInit; exampleCTS.step s1) =
    some { data := [true], phase := 0 } := by
  native_decide

end TagSystem
