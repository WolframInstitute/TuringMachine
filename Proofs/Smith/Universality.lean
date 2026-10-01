/-
  Smith.Universality

  PLAN.md target T8 (milestone M8), with the closed-form initial condition
  of milestone M9: the headline theorem. For every run of `n` steps of a
  well-formed binary Turing machine from a valid configuration, the
  wolfram23 machine started on `IC tm c n` reproduces those `n` steps at a
  strictly increasing schedule of times and then exits to the right in
  state A (`wolfram23_universal_ic`). `IC tm c n` is a definition: the
  encoders of T7 (`TagSystem.TMToCTS`, the Cocke-Minsky simulation of the
  machine by a cyclic tag system) and T4 (`Smith.ClosedForm`), applied with
  a budget `icN c n` and parameters computed from the machine, the
  configuration and `n` by closed-form bounds; it runs no system.
  `wolfram23_universal`, the form with an existential initial condition, is
  a corollary. See `Smith/Infinite.lean` for T6, the infinite form.

  The cyclic tag system of T7 makes one cycle of its `2 (1 + 84 S)`
  appendants per tag step. The tag system carries out every step of the
  machine, including the steps of the halting state (`TagSystem.TagBounds`),
  so its run lasts any budget; its time for `n` machine steps is at most
  `icN c n = n * 15 * 2 ^ (sz c + n)`. The decoder `decodeTM` is the
  composite of the decoders: `decodeW23` reads the doubled cyclic tag word
  off the wolfram23 tape, `undbl` the cyclic tag word, `decodeCTS` the
  configuration of the machine (without trailing blanks, `canon`).

  Contents: `undbl`, `decodeTM`, `ctsOf`, `icN`, `icProg`, `IC`, `ICw`,
  `ICb`, `cts_run_tag`, `wolfram23_universal_ic`, `wolfram23_universal`.
-/

import Smith.ClosedForm
import TagSystem.TagBounds

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

/-! ## T8 with the closed-form initial condition -/

/-- The cyclic tag system of T7 for the machine `tm`. -/
def ctsOf (tm : Machine) : CTS := tagToCTS (tagK tm tm.numStates) (K_pos _)

/-- The budget of the closed-form initial condition: a bound on the tag time
    of `n` machine steps from `c` (`tagTime_le`), in cycles of the cyclic
    tag system, one cycle per tag step. -/
def icN (c : Config) (n : Nat) : Nat := n * 15 * 2 ^ (sz c + n)

/-- The System 5 program of the closed-form initial condition. -/
def icProg (tm : Machine) (c : Config) (n : Nat) : System5Config :=
  ctsToSystem5 (ctsOf tm) (ctsOfCfg tm.numStates c) (icN c n)

/-- The closed-form initial condition for `n` steps of `tm` from `c`: every
    part of it (the tag system, the cyclic tag system, the System 5 program
    with `icN c n` cycles, the System 4 tape, the parity blocks of width
    `2 ^ ICw tm c n`) is computed from `tm`, `c` and `n` by the encoders
    and the closed-form parameters, without running any system. -/
def IC (tm : Machine) (c : Config) (n : Nat) : BiTM.Config := icStart (icProg tm c n)

/-- The width exponent of the parity blocks of `IC tm c n`. -/
def ICw (tm : Machine) (c : Config) (n : Nat) : Nat := icW (icProg tm c n)

/-- The band of the decoder for `IC tm c n`. -/
def ICb (tm : Machine) (c : Config) (n : Nat) : Nat := icBand (icProg tm c n)

theorem length_ge_two_of_stepP {σ : Type} (P : σ → List σ) (w w' : List σ)
    (h : stepP P w = some w') : 2 ≤ w.length := by
  match w, h with
  | _ :: _ :: _, _ => simp

/-- The cyclic tag run of T7 from the encoding of a valid configuration at
    tag time `t`: defined, and the encoding of the tag word, which is the
    word of the `i`-th configuration at tag time `tagTime tm c i`. -/
theorem cts_run_tag (tm : Machine) (hwf : WF tm) (c : Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) (t : Nat) :
    ∃ w, nStepsP (prod tm) (word c) t = some w ∧ WordOK tm.numStates w ∧
      (ctsOf tm).nSteps (ctsOfCfg tm.numStates c) (2 * (1 + 84 * tm.numStates) * t)
        = some (tagConfigToCTS (1 + 84 * tm.numStates) (w.map (enc tm.numStates))) := by
  obtain ⟨w, hw⟩ := tag_run_total tm hwf c hv hst t
  have hn : ∀ q h, q < tm.numStates → nxt tm q h < tm.numStates := fun q h hq => WF_nxt tm hwf q h hq
  have hwOK : WordOK tm.numStates (word c) := WordOK_cword _ _ _ _ hst
  have henc := nStepsP_enc tm tm.numStates hn t (word c) hwOK
  rw [hw, Option.map_some] at henc
  refine ⟨w, hw, ?_, cts_of_tag (tagK tm tm.numStates) (K_pos _) t _ _ henc⟩
  -- the tag words stay in the alphabet
  clear henc
  induction t generalizing w with
  | zero =>
    rw [nStepsP_zero] at hw
    obtain rfl := Option.some.inj hw
    exact hwOK
  | succ t ih =>
    obtain ⟨w0, hw0⟩ := nStepsP_some_of_le (prod tm) (word c) t (t + 1) (by omega) w hw
    have hw0OK := ih w0 hw0
    have e : nStepsP (prod tm) (word c) (t + 1) = (nStepsP (prod tm) (word c) t).bind (stepP (prod tm)) := by
      rw [nStepsP_add]
      cases nStepsP (prod tm) (word c) t with
      | none => rfl
      | some v => simp only [Option.bind_some, nStepsP_succ, nStepsP_zero]; cases stepP (prod tm) v <;> rfl
    rw [e, hw0, Option.bind_some] at hw
    exact stepP_OK tm tm.numStates hn w0 w hw0OK hw

/-- T8 with the closed-form initial condition. For a well-formed binary
    Turing machine `tm`, a valid configuration `c` with state below
    `numStates` and a run of `n` steps of `tm` from `c`, wolfram23 started on
    `IC tm c n` decodes, by `decodeTM` with the block width `2 ^ ICw tm c n`
    and the band `ICb tm c n`, to the configurations of the run at strictly
    increasing times, stays on its tape until then, and leaves it to the
    right in state A. The tape is a definition computed from `tm`, `c` and
    `n` by the encoders and closed-form bounds; it does not run the machine
    or any of the emulating systems. -/
theorem wolfram23_universal_ic (tm : Machine) (hwf : WF tm) (c : Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) (n : Nat) (c' : Config) (hrun : BiTM.nSteps tm c n = some c') :
    ∃ (times : Nat → Nat) (T : Nat),
      IsValidWolfram23Cfg (IC tm c n) ∧ (IC tm c n).state = 1 ∧
      (∀ i, i < n → times i < times (i + 1)) ∧
      (∀ i, i ≤ n → times i ≤ T ∧
        ∃ ci cfgi, BiTM.nSteps tm c i = some ci ∧ BiTM.nSteps wolfram23 (IC tm c n) (times i) = some cfgi ∧
          decodeTM tm.numStates (2 ^ ICw tm c n) (ICb tm c n) cfgi = some (canon ci)) ∧
      (∀ τ, τ ≤ T → ∃ cfgτ, BiTM.nSteps wolfram23 (IC tm c n) τ = some cfgτ ∧
        biSize cfgτ = biSize (IC tm c n)) ∧
      (∃ L : List Nat, BiTM.nSteps wolfram23 (IC tm c n) (T + 1) = some ⟨1, L, 0, []⟩ ∧
        L.length = biSize (IC tm c n)) := by
  obtain ⟨K, hK⟩ : ∃ K, K = 1 + 84 * tm.numStates := ⟨_, rfl⟩
  have hlen : (ctsOf tm).appendants.length = 2 * K := by
    rw [hK]; exact tagToCTS_appendants_length _ _
  obtain ⟨N, hN⟩ : ∃ N, N = icN c n := ⟨_, rfl⟩
  -- the cyclic tag run lasts the budget and leaves a nonempty word
  obtain ⟨wN1, hwN1, -, -⟩ := cts_run_tag tm hwf c hv hst (N + 1)
  obtain ⟨wN, hwN, -, hctsN⟩ := cts_run_tag tm hwf c hv hst N
  have hwN2 : 2 ≤ wN.length := by
    rw [nStepsP_add, hwN, Option.bind_some] at hwN1
    rw [nStepsP_succ] at hwN1
    cases hs : stepP (prod tm) wN with
    | none => rw [hs] at hwN1; cases hwN1
    | some v => exact length_ge_two_of_stepP _ _ _ hs
  have hne : (tagConfigToCTS (1 + 84 * tm.numStates) (wN.map (enc tm.numStates))).data ≠ [] := by
    show tagWordEncode _ _ ≠ []
    intro h
    have h1 := tagWordEncode_length (1 + 84 * tm.numStates) (wN.map (enc tm.numStates))
    rw [h, List.length_nil, List.length_map] at h1
    have : 0 < (1 + 84 * tm.numStates) * wN.length := Nat.mul_pos (by omega) (by omega)
    omega
  have hrunC : (ctsOf tm).nSteps (ctsOfCfg tm.numStates c) ((ctsOf tm).appendants.length * N)
      = some (tagConfigToCTS (1 + 84 * tm.numStates) (wN.map (enc tm.numStates))) := by
    rw [hlen, hK]; exact hctsN
  obtain ⟨times', T, hvalid, hstate, hmono', htr', hconf, hexit⟩ :=
    conjecture0_closed (ctsOf tm) (ctsOfCfg tm.numStates c) N _ hrunC hne
  have hIC : IC tm c n = icStart (ctsToSystem5 (ctsOf tm) (ctsOfCfg tm.numStates c) N) := by
    rw [hN]; rfl
  have hICw : ICw tm c n = icW (ctsToSystem5 (ctsOf tm) (ctsOfCfg tm.numStates c) N) := by
    rw [hN]; rfl
  have hICb : ICb tm c n = icBand (ctsToSystem5 (ctsOf tm) (ctsOfCfg tm.numStates c) N) := by
    rw [hN]; rfl
  rw [hIC, hICw, hICb]
  -- the tag times of the machine's steps fit in the budget
  have htag_le : ∀ i, i ≤ n → tagTime tm c i ≤ N := by
    intro i hi
    have h1 := tagTime_mono tm c i n hi
    have h2 := tagTime_le tm hwf c hv hst n
    rw [hN]; unfold icN; omega
  have hK1 : 1 ≤ K := by omega
  refine ⟨fun i => times' (2 * K * tagTime tm c i), T, hvalid, hstate, ?_, ?_, hconf, hexit⟩
  · intro i hi
    have h1 : tagTime tm c i < tagTime tm c (i + 1) := tagTime_strictMono tm c i (i + 1) (by omega)
    have h2 := htag_le (i + 1) hi
    have h3 : 2 * K * tagTime tm c i < 2 * K * tagTime tm c (i + 1) :=
      Nat.mul_lt_mul_of_pos_left h1 (by omega)
    have h4 : 2 * K * tagTime tm c (i + 1) ≤ (ctsOf tm).appendants.length * N := by
      rw [hlen]; exact Nat.mul_le_mul_left _ h2
    exact strictMono_of_succ times' _ hmono' _ _ h3 h4
  · intro i hi
    have hle : 2 * K * tagTime tm c i ≤ (ctsOf tm).appendants.length * N := by
      rw [hlen]; exact Nat.mul_le_mul_left _ (htag_le i hi)
    obtain ⟨hT, ci', cfgi, hci', hcfgi, hdec⟩ := htr' _ hle
    obtain ⟨ci, hci⟩ := StepSys.nSteps_some_of_le (tmSys tm) c c' n i hi
      (by rw [tmSys_nSteps]; exact hrun)
    rw [tmSys_nSteps] at hci
    have hraw := rawRun_eq tm c i ci hci
    obtain ⟨hvi, hsti⟩ := rawRun_valid tm hwf c hv hst i
    rw [hraw] at hvi hsti
    -- the cyclic tag configuration at that time is the encoding of `ci`
    have hn' : ∀ q h, q < tm.numStates → nxt tm q h < tm.numStates := fun q h hq => WF_nxt tm hwf q h hq
    have htagi := tag_rawRun tm hwf c hv hst i
    rw [hraw] at htagi
    have henc := nStepsP_enc tm tm.numStates hn' (tagTime tm c i) (word c) (WordOK_cword _ _ _ _ hst)
    rw [htagi, Option.map_some] at henc
    have hctsi := cts_of_tag (tagK tm tm.numStates) (K_pos _) (tagTime tm c i) _ _ henc
    have hctsi' : (ctsOf tm).nSteps (ctsOfCfg tm.numStates c) (2 * K * tagTime tm c i)
        = some (ctsOfCfg tm.numStates ci) := by
      rw [hK]; exact hctsi
    rw [hctsi'] at hci'
    obtain rfl := Option.some.inj hci'
    refine ⟨hT, ci, cfgi, hci, hcfgi, ?_⟩
    unfold decodeTM
    rw [hdec, Option.bind_some, undbl_dbl, Option.bind_some]
    exact decodeCTS_word tm.numStates ci hvi hsti

/-- T8 with an existential initial condition, a corollary of
    `wolfram23_universal_ic`: for a well-formed binary Turing machine `tm`, a
    valid configuration `c` with state below `numStates`, and a run of `n`
    steps of `tm` from `c`, there are a wolfram23 configuration `start`, a
    block width `2^w`, a band `b`, strictly increasing times `times i` and an
    exit time `T` such that `start` is valid and in state A; at time
    `times i` the wolfram23 tape decodes, by `decodeTM`, to the `i`-th
    configuration of the run of `tm` (without trailing blanks); up to time
    `T` the run of wolfram23 stays on its explicit tape; and at time `T + 1`
    its head is on the cell right of the tape, a 0, in state A. -/
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
  obtain ⟨times, T, h1, h2, h3, h4, h5, h6⟩ := wolfram23_universal_ic tm hwf c hv hst n c' hrun
  exact ⟨IC tm c n, ICw tm c n, ICb tm c n, times, T, h1, h2, h3, h4, h5, h6⟩

end Smith
