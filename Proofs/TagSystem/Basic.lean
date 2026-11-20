/-
  TagSystem.Basic

  Formalization of 2-tag systems and cyclic tag systems.
  These are intermediate computational models in universality proofs:
    Turing Machine -> 2-Tag System -> Cyclic Tag System -> (Rule 110 / (2,3) TM)

  Canonical home: TuringMachineSearch/Proofs/TagSystem/
  Imported by both Rule110 and BiTM universality proofs.
-/

import Smith.StepSys

namespace TagSystem

universe u

-- ============================================================================
-- 2-Tag Systems
-- ============================================================================

/-- A 2-tag system over a finite alphabet of size k.
    Each step: read the first symbol, delete the first 2 symbols,
    append the production for the read symbol. -/
structure Tag (k : Nat) where
  /-- Production rules: for each symbol i in Fin k, the string to append -/
  productions : Fin k → List (Fin k)

/-- Configuration of a tag system: just the current data word -/
abbrev TagConfig (k : Nat) := List (Fin k)

/-- The 2-tag step with productions `P`: read the first symbol, delete the
    first two, append the production of the symbol read; `none` on a word of
    fewer than two symbols. -/
def stepP {σ : Type u} (P : σ → List σ) : List σ → Option (List σ)
  | [] => none
  | [_] => none
  | a :: _ :: rest => some (rest ++ P a)

/-- Single step of a 2-tag system. -/
def Tag.step {k : Nat} (ts : Tag k) (cfg : TagConfig k) : Option (TagConfig k) :=
  stepP ts.productions cfg

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

/-- A cyclic tag system as a step system. -/
def ctsSys (cts : CTS) : Smith.StepSys CTSConfig := ⟨cts.step⟩

/-- Run CTS for exactly n steps -/
def CTS.nSteps (cts : CTS) (cfg : CTSConfig) (n : Nat) : Option CTSConfig := (ctsSys cts).nSteps cfg n

end TagSystem
