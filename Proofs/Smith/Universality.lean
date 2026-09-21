/-
  Smith.Universality

  PLAN.md target T8 (milestone M8): the headline theorem. For every run of
  `n` steps of a well-formed binary Turing machine from a valid
  configuration there is a finite initial tape, depending on the machine,
  the configuration and `n`, from which the wolfram23 machine reproduces
  those `n` steps at a strictly increasing schedule of times and then exits
  to the right in state A. The one-tape-per-machine-and-input form is
  `wolfram23_infinite` in `Smith/Infinite.lean`. T8 is T4
  (`Smith.Conjecture0`, Smith's finite-form Conjecture 0) composed with T7
  (`TagSystem.TMToCTS`, the Cocke-Minsky simulation of the machine by a
  cyclic tag system). See `Smith/Infinite.lean` for T6, the infinite form.

  The cyclic tag system of T7 makes one cycle of its `2 (1 + 84 S)`
  appendants per tag step, so the budget of cycles T4 needs is the number of
  tag steps of the run, which the tag-level schedule `tm_tag_forwardSim`
  gives. The decoder `decodeTM` is the composite of the decoders: `decodeW23`
  reads the doubled cyclic tag word off the wolfram23 tape, `undbl` the
  cyclic tag word, `decodeCTS` the configuration of the machine (without
  trailing blanks, `canon`).

  Contents: `undbl`, `decodeTM`, `wolfram23_universal`.
-/

import Smith.Conjecture0
import TagSystem.TMToCTS

namespace Smith

open TM
open BiTM
open TagSystem

/-- The inverse of `dbl` on doubled words; `none` on any other word. -/
def undbl : List Bool → Option (List Bool)
  | [] => some []
  | [_] => none
  | a :: b :: rest => if a = b then (undbl rest).map (a :: ·) else none

theorem undbl_dbl (w : List Bool) : undbl (dbl w) = some w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [dbl, undbl, ih]

/-- The decoder of the wolfram23 tape for a machine with states below `S`:
    the doubled cyclic tag word (`decodeW23`, blocks of width `N`, band `b`),
    undoubled, read as a configuration of the machine (`decodeCTS`). -/
def decodeTM (S N b : Nat) (cfg : BiTM.Config) : Option Config :=
  (decodeW23 N b cfg).bind fun d => (undbl d).bind fun data => decodeCTS S ⟨data, 0⟩

/-- T8. For a well-formed binary Turing machine `tm`, a valid configuration
    `c` with state below `numStates`, and a run of `n` steps of `tm` from `c`,
    there are a wolfram23 configuration `start`, a block width `2^w`, a band
    `b`, strictly increasing times and an exit time `T` such that: `start` is
    valid and in state A; at time `times i` the wolfram23 tape decodes, by
    `decodeTM`, to the `i`-th configuration of the run of `tm` (without
    trailing blanks); up to time `T` the run of wolfram23 stays on its
    explicit tape; and at time `T + 1` its head is on the cell right of the
    tape, a 0, in state A. -/
theorem wolfram23_universal (tm : Machine) (hwf : WF tm) (c : Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) (n : Nat) (c' : Config) (hrun : BiTM.nSteps tm c n = some c') :
    ∃ (start : BiTM.Config) (w b : Nat) (times : Nat → Nat) (T : Nat),
      IsValidWolfram23Cfg start ∧ start.state = 1 ∧
      (∀ i, i < n → times i < times (i + 1)) ∧
      (∀ i, i ≤ n → times i ≤ T ∧
        ∃ ci cfgi, BiTM.nSteps tm c i = some ci ∧ BiTM.nSteps wolfram23 start (times i) = some cfgi ∧
          decodeTM tm.numStates (2 ^ w) b cfgi = some (canon ci)) ∧
      (∀ τ, τ ≤ T → ∃ cfgτ, BiTM.nSteps wolfram23 start τ = some cfgτ ∧ biSize cfgτ = biSize start) ∧
      (∃ L : List Nat, BiTM.nSteps wolfram23 start (T + 1) = some ⟨1, L, 0, []⟩ ∧
        L.length = biSize start) := by
  obtain ⟨tt, ht0, htmono, httr⟩ := ForwardSim_nSteps (tm_tag_forwardSim tm hwf) n c
    ((word c).map (enc tm.numStates)) ⟨hv, hst, rfl⟩ c' (by rw [tmSys_nSteps]; exact hrun)
  have httle : ∀ j, j ≤ n → tt j ≤ tt n := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact le_of_lt (strictMono_of_succ tt n htmono j n hlt (le_refl _))
    · exact le_refl _
  have hlen := tagToCTS_appendants_length (tagK tm tm.numStates) (K_pos tm.numStates)
  obtain ⟨cn, wn, hcn, hwn, -, -, rfl⟩ := httr n (le_refl n)
  rw [tagSysK_nSteps] at hwn
  have hcts_n := cts_of_tag (tagK tm tm.numStates) (K_pos _) (tt n) _ _ hwn
  have hne : (tagConfigToCTS (1 + 84 * tm.numStates) ((word cn).map (enc tm.numStates))).data ≠ [] := by
    show tagWordEncode _ _ ≠ []
    intro h
    have h1 := tagWordEncode_length (1 + 84 * tm.numStates) ((word cn).map (enc tm.numStates))
    rw [h, List.length_nil, List.length_map] at h1
    have h2 := length_word cn
    have h3 : 0 < (1 + 84 * tm.numStates) * (word cn).length := Nat.mul_pos (by omega) (by omega)
    omega
  obtain ⟨start, w, b, times', T, hvalid, hstate, hmono', htr', hconf, hexit⟩ :=
    conjecture0_finite (tagToCTS (tagK tm tm.numStates) (K_pos _)) (ctsOfCfg tm.numStates c) (tt n) _
      (by rw [hlen]; exact hcts_n) hne
  have hpos : 0 < 2 * (1 + 84 * tm.numStates) := by omega
  refine ⟨start, w, b, fun i => times' (2 * (1 + 84 * tm.numStates) * tt i), T, hvalid, hstate,
    ?_, ?_, hconf, hexit⟩
  · intro i hi
    have h1 := htmono i hi
    have h2 := httle (i + 1) hi
    exact strictMono_of_succ times' _ hmono' _ _ (Nat.mul_lt_mul_of_pos_left h1 hpos)
      (by rw [hlen]; exact Nat.mul_le_mul_left _ h2)
  · intro i hi
    have hle : 2 * (1 + 84 * tm.numStates) * tt i
        ≤ (tagToCTS (tagK tm tm.numStates) (K_pos _)).appendants.length * tt n := by
      rw [hlen]; exact Nat.mul_le_mul_left _ (httle i hi)
    obtain ⟨hT, ci', cfgi, hci', hcfgi, hdec⟩ := htr' _ hle
    obtain ⟨ci, wi, hci, hwi, hvi, hsti, rfl⟩ := httr i hi
    rw [tagSysK_nSteps] at hwi
    have hcts_i := cts_of_tag (tagK tm tm.numStates) (K_pos _) (tt i) _ _ hwi
    rw [show ctsOfCfg tm.numStates c
        = tagConfigToCTS (1 + 84 * tm.numStates) ((word c).map (enc tm.numStates)) from rfl,
      hcts_i] at hci'
    obtain rfl := Option.some.inj hci'
    refine ⟨hT, ci, cfgi, by rw [← tmSys_nSteps]; exact hci, hcfgi, ?_⟩
    unfold decodeTM
    rw [hdec, Option.bind_some, undbl_dbl, Option.bind_some]
    exact decodeCTS_word tm.numStates ci hvi hsti

end Smith
