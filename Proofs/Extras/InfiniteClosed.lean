/-
  Extras.InfiniteClosed

  T6 with the tape in closed form (milestone M9, open item 1), an optional
  corollary of the development: block `k` is `closedBlock tm c k`, built
  from the closed-form System 5 program `icProg tm c k` of
  `Smith.UniversalityClosed`, with guards and width sized by the run bounds
  of `Smith.RunBounds` (`System4.run_bound`); `ITape tm c`, the
  concatenation of these blocks, is a definition that runs no system, and
  `wolfram23_infinite_ic` is `wolfram23_infinite` on that tape.

  Contents: `blkProg`, `blkN`, `blkR`, `blkOrig`, `blkH`, `blkW`,
  `closedBlock`, `block_exists_closed`, `ITape`, `wolfram23_infinite_ic`.
-/

import Wolfram23.Infinite.T6
import Extras.UniversalityClosed

namespace Smith

open TM
open BiTM
open LState
open TagSystem

/-! ## The closed-form blocks

Block `k` is built from the closed-form System 5 program `icProg tm c k`
of T8 (the cyclic tag system of the machine with `icN c k` cycles): its
program is the System 4 tape of that program with the parameter `icF`, its
guards are sized by the bound `icT4` on the program's System 4 run, and its
width by the bound `blkH` on the block's own System 4 run
(`System4.run_bound`). Every field of `closedBlock tm c k` other than the
run data `H` and `dt` (which only the proofs read) is a closed form of
`tm`, `c` and `k`. -/

/-- The System 5 program of block `k`. -/
def blkProg (tm : Machine) (c : Config) (k : Nat) : System5Config := icProg tm c k

/-- The guard parameter `n` of block `k`. -/
def blkN (tm : Machine) (c : Config) (k : Nat) : Nat := icT4 (blkProg tm c k) + 3

/-- The number of guards `r` of block `k`. -/
def blkR (tm : Machine) (c : Config) (k : Nat) : Nat := icT4 (blkProg tm c k) + 1

/-- The program tape of block `k`. -/
def blkOrig (tm : Machine) (c : Config) (k : Nat) : List System4Elem :=
  System4Elem.set (encodeBag (blkProg tm c k).bag) :: icRest (blkProg tm c k)

/-- A bound on the System 4 run of block `k`. -/
def blkH (tm : Machine) (c : Config) (k : Nat) : Nat :=
  (2 * (blockTape (blkN tm c k) (blkR tm c k) (blkOrig tm c k)).length + 2) *
    ((blockTape (blkN tm c k) (blkR tm c k) (blkOrig tm c k)).length + 1)

/-- The width exponent of block `k`: the bit length of the fuel, the guard
    parameter and the bound on the set elements, so that the block width
    `2 ^ blkW` is linear in them. -/
def blkW (tm : Machine) (c : Config) (k : Nat) : Nat :=
  Nat.size (blkH tm c k + icBand (blkProg tm c k) + blkN tm c k + 3 * icF (blkProg tm c k) + 6)

/-- Block `k` in closed form (the run data `H`, `dt` set to 0; see
    `block_exists_closed` for the actual ones). -/
def closedBlock (tm : Machine) (c : Config) (k : Nat) : BlockData :=
  ⟨blkN tm c k, blkR tm c k, blkW tm c k, icBand (blkProg tm c k),
    encodeBag (blkProg tm c k).bag, icRest (blkProg tm c k), 0, fun _ => 0⟩

/-- Block `k` emulates the first `k` raw steps of the machine: the closed-form
    block with its actual run length and decoding times meets `BlockSpec`. -/
theorem block_exists_closed (tm : Machine) (hwf : WF tm) (c : BiTM.Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) (k : Nat) :
    ∃ (H : Nat) (dt : Nat → Nat), BlockSpec tm c k { closedBlock tm c k with H := H, dt := dt } := by
  obtain ⟨K, hK⟩ : ∃ K, K = 1 + 84 * tm.numStates := ⟨_, rfl⟩
  have hlen : (ctsOf tm).appendants.length = 2 * K := by
    rw [hK]; exact tagToCTS_appendants_length _ _
  obtain ⟨N, hN⟩ : ∃ N, N = icN c k := ⟨_, rfl⟩
  -- the cyclic tag run lasts the budget and leaves a nonempty word
  obtain ⟨wN1, hwN1, -, -⟩ := cts_run_tag tm hwf c hv hst (N + 1)
  obtain ⟨wN, hwN, -, hctsN⟩ := cts_run_tag tm hwf c hv hst N
  have hwN2 : 2 ≤ wN.length := by
    rw [nStepsP_add, hwN, Option.bind_some, nStepsP_succ] at hwN1
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
  -- the System 4 emulation of that cyclic tag run
  obtain ⟨T4, cE, t4, hT4le, hrunT4, hstE, hactE, h4mono, h4tr⟩ :=
    system4_emulation_closed (ctsOf tm) (ctsOfCfg tm.numStates c) N _ hrunC hne
  obtain ⟨hf1, hbag1, hrules0⟩ := icF_facts (ctsOf tm) (ctsOfCfg tm.numStates c) N
  have hs : ctsToSystem5 (ctsOf tm) (ctsOfCfg tm.numStates c) N = blkProg tm c k := by
    rw [hN]; rfl
  rw [hs] at hT4le hrunT4 h4tr hf1 hbag1 hrules0
  obtain ⟨s, hsd⟩ : ∃ s, s = blkProg tm c k := ⟨_, rfl⟩
  rw [← hsd] at hT4le hrunT4 h4tr hf1 hbag1 hrules0
  have hrules1 : ∀ r ∈ s.rules, ∀ x ∈ r, 0 ≤ x ∧ x < icF s := by
    intro r hr x hx
    have := (hrules0 r hr).2 x hx
    constructor <;> omega
  have hpos : 0 < 2 * K := by omega
  have hT4 : 1 ≤ T4 := by
    have := (h4tr 0 (Nat.zero_le _)).1
    omega
  have hc40 : system5ToSystem4 s (icF s) = ⟨blkOrig tm c k, 0, System4State.A⟩ := by
    rw [hsd]; rfl
  rw [hc40] at hrunT4 h4tr
  obtain ⟨n, hn⟩ : ∃ n, n = blkN tm c k := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = blkR tm c k := ⟨_, rfl⟩
  have hne' : n = icT4 s + 3 := by rw [hn, hsd]; rfl
  have hre : r = icT4 s + 1 := by rw [hr, hsd]; rfl
  have horig : blkOrig tm c k = System4Elem.set (encodeBag s.bag) :: icRest s := by rw [hsd]; rfl
  rw [horig] at hrunT4 h4tr
  obtain ⟨H, padT, turns, hH, hsafe, hpmono, hptr⟩ :=
    block_run n r (by omega) (encodeBag s.bag) (icRest s) T4 cE hT4 (by omega) (by omega) hrunT4 hactE
  have hHle : H ≤ blkH tm c k := by
    have := System4.run_bound _ H _ hH
    rw [blkH, ← hn, ← hr, horig]
    exact this
  obtain ⟨w, hw⟩ : ∃ w, w = blkW tm c k := ⟨_, rfl⟩
  have hw2 : blkH tm c k + icBand s + n + 3 * icF s + 6 < 2 ^ w := by
    rw [hw, blkW, ← hn, ← hsd]; exact Nat.lt_size_self _
  have hwf4 := system5ToSystem4_wellFormed s (icF s) hf1
  have hlast4 := system5ToSystem4_last_set s (icF s) hf1
  rw [hc40, horig] at hwf4 hlast4
  -- decoding times: the tag times of the raw steps
  have htag_le : ∀ i, i ≤ k → 2 * K * tagTime tm c i ≤ (ctsOf tm).appendants.length * N := by
    intro i hi
    rw [hlen]
    apply Nat.mul_le_mul_left
    have h1 := tagTime_mono tm c i k hi
    have h2 := tagTime_le tm hwf c hv hst k
    rw [hN]; unfold icN; omega
  refine ⟨H, fun i => 2 * r + padT (t4 (2 * K * tagTime tm c i)), ?_⟩
  have hcl : closedBlock tm c k = ⟨n, r, w, icBand s, encodeBag s.bag, icRest s, 0, fun _ => 0⟩ := by
    rw [hn, hr, hw, hsd]; rfl
  rw [hcl]
  refine ⟨?_, ?_, ?_, hwf4, hlast4, ?_, hsafe _, ⟨_, hH, ?_, ?_⟩, ?_, ?_⟩
  · show 3 ≤ n; omega
  · show H + icBand s + 3 ≤ 2 ^ w; omega
  · show n < 2 ^ w; omega
  · intro S hS e he
    have := system5ToSystem4_elem_lt s (icF s) hbag1 hrules1 S (by rw [hc40, horig]; exact hS) e he
    show 0 ≤ e ∧ e.toNat < 2 ^ w
    constructor <;> omega
  · simp only [padCfg]; exact hstE
  · simp only [padCfg, List.length_append, List.length_singleton, length_guardPairs, sets,
      List.length_map, length_merged, List.length_nil, hactE]
    omega
  · intro i hi
    show 2 * r + padT (t4 (2 * K * tagTime tm c i)) < 2 * r + padT (t4 (2 * K * tagTime tm c (i + 1)))
    have h1 := tagTime_strictMono tm c i (i + 1) (by omega)
    have h3 := htag_le (i + 1) hi
    have h4 : t4 (2 * K * tagTime tm c i) < t4 (2 * K * tagTime tm c (i + 1)) :=
      strictMono_of_succ t4 _ h4mono _ _ (Nat.mul_lt_mul_of_pos_left h1 hpos) h3
    have h5 := (h4tr (2 * K * tagTime tm c (i + 1)) h3).1
    have := strictMono_of_succ padT (T4 - 1) hpmono _ _ h4 (by omega)
    omega
  · intro i hi
    obtain ⟨hT, ci', Kl, R, hci', hKne, hc4i, hdec⟩ := h4tr _ (htag_le i hi)
    -- the cyclic tag configuration at that time is the encoding of the raw configuration
    have hn' : ∀ q h, q < tm.numStates → nxt tm q h < tm.numStates := fun q h hq => WF_nxt tm hwf q h hq
    have henc := nStepsP_enc tm tm.numStates hn' (tagTime tm c i) (word c) (WordOK_cword _ _ _ _ hst)
    rw [tag_rawRun tm hwf c hv hst i, Option.map_some] at henc
    have hctsi := cts_of_tag (tagK tm tm.numStates) (K_pos _) (tagTime tm c i) _ _ henc
    have hctsi' : (ctsOf tm).nSteps (ctsOfCfg tm.numStates c) (2 * K * tagTime tm c i)
        = some (ctsOfCfg tm.numStates (rawRun tm c i)) := by
      rw [hK]; exact hctsi
    rw [hctsi'] at hci'
    obtain rfl := Option.some.inj hci'
    obtain ⟨hpt, ci4, hci4, hpad⟩ := hptr (t4 (2 * K * tagTime tm c i)) hT
    rw [hc4i] at hci4
    obtain rfl := Option.some.inj hci4
    refine ⟨hpt,
      [System4Elem.star] ++ guardPairs n (r - 1 - turns (t4 (2 * K * tagTime tm c i)))
        ++ sets (merged n (turns (t4 (2 * K * tagTime tm c i)))),
      Kl, R, hKne, ?_, hdec⟩
    show System4.nSteps ⟨blockTape n r (System4Elem.set (encodeBag s.bag) :: icRest s), 0,
      System4State.C⟩ _ = _
    rw [hpad]
    simp only [padCfg, List.append_assoc, List.append_nil, List.length_append,
      List.length_singleton, length_guardPairs, sets, List.length_map, length_merged,
      Nat.add_zero, Nat.add_assoc]

/-- The closed-form right-infinite tape of T6: the cells of the closed-form
    blocks `closedBlock tm c 0`, `closedBlock tm c 1`, ... after a 0. Cell
    `i` is a closed form of `tm`, `c` and `i`; no system is run to compute
    it. -/
def ITape (tm : Machine) (c : Config) : Nat → Nat := tape (closedBlock tm c)

/-- T6 (PLAN.md section 2), Smith's Conjecture 0 in infinite form, with the
    tape in closed form. For a well-formed binary machine `tm` and a valid
    configuration `c`, wolfram23 started at the left end of the tape
    `ITape tm c` in state B on a 2 runs forever without ever moving left
    from the first cell, and emulates the run of `tm` from `c`: for every
    `k` there are a window `W` and strictly increasing times, the last of
    them later than `k`, such that at time `times i` for `i <= k` wolfram23
    is in state B and, whenever the `i`-th configuration of the run exists,
    the cells right of the head decode by `decodeTM`, with the block width
    `2 ^ blkW tm c k` and the band `icBand (blkProg tm c k)` of block `k`,
    on the window `W` and on every larger window, to that configuration
    (without trailing blanks). Block `k` of the tape re-emulates the first
    `k` steps with its own width and band, as in Smith's construction; the
    decoder reads only the head and the cells to its right up to the first
    0. -/
theorem wolfram23_infinite_ic (tm : Machine) (hwf : WF tm) (c : Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) :
    (∀ i, ITape tm c i < 3) ∧
      (∀ τ, ∃ d, inSteps wolfram23 (istart (ITape tm c)) τ = some d ∧
        (d.left = [] → (wolfram23.transition d.state d.head).dir = Dir.R)) ∧
      ∀ k, ∃ (W : Nat) (times : Nat → Nat), k < times k ∧
        (∀ i, i < k → times i < times (i + 1)) ∧
        (∀ i ci, i ≤ k → BiTM.nSteps tm c i = some ci → ∃ d,
          inSteps wolfram23 (istart (ITape tm c)) (times i) = some d ∧ d.state = 2 ∧
          ∀ W', W ≤ W' → decodeTM tm.numStates (2 ^ blkW tm c k) (icBand (blkProg tm c k))
            (truncI W' d) = some (canon ci)) := by
  choose H dt hbd using block_exists_closed tm hwf c hv hst
  have htape : tape (fun j => { closedBlock tm c j with H := H j, dt := dt j }) = ITape tm c := rfl
  rw [← htape]
  refine ⟨tape_lt _, fun τ => ?_, fun k => ?_⟩
  · obtain ⟨dτ, hdτ, -⟩ := inSteps_valid _ (istart_valid _ (tape_lt _)) τ
    obtain ⟨-, times, hkt, -, hleft, -⟩ := stage_infinite tm hwf c hv hst _ hbd τ
    exact ⟨dτ, hdτ, hleft τ hkt dτ hdτ⟩
  · obtain ⟨W, times, hkt, hmono, -, hdec⟩ := stage_infinite tm hwf c hv hst _ hbd k
    exact ⟨W, times, hkt, hmono, hdec⟩

end Smith
