/-
  Smith.ClosedForm

  Open item 1 (PLAN.md milestone M9): the closed-form initial condition.
  The tape of T4 (`conjecture0_finite`) and T8 (`wolfram23_universal`) was
  existential, its parameters chosen in the proof from the lengths of the
  emulation's own runs (the System 5 time `t5 n`, the System 4 exit time,
  the tag time of the machine's run). Here every such length is replaced by
  a bound computed from the program text and from the size of the machine's
  configuration, so the initial condition becomes a definition that runs no
  system: `icStart s` for a System 5 program `s`, and `IC tm c n` for a
  machine, a configuration and a number of steps.

  The parameters of `icStart s`, in order (each a closed form of the ones
  before and of `s`):
    * `icB s`, the largest integer of `s` (`maxInt5`, read off the program);
    * `icT5 s = icB s * 2 ^ (number of rules)`, above every System 5 run
      from `s` (`System5.run_bound`);
    * `icM`, `icH`, `icF`, `icBand` as in T4, with `icT5` in place of the
      System 5 run length;
    * `icT4 s = (2 L + 2) (L + 1)` for the length `L` of the System 4 tape
      `system5ToSystem4 s (icF s)`, above every System 4 run
      (`System4.run_bound`);
    * `icFuel = icT4 + icBand` and `icW = icFuel + 3 icF + 6`.
  Every hypothesis T4 places on its parameters is an inequality that holds
  for any value at least the exact run length, so the proof of T4 goes
  through with the bounds (`conjecture0_closed`).

  Contents: `icB`, `icT5`, `icM`, `icH`, `icF`, `icBand`, `icRest`,
  `icLen4`, `icT4`, `icFuel`, `icW`, `icStart`, `Inv5_ctsToSystem5`,
  `icF_facts`, `system4_emulation`, `conjecture0_closed`,
  `conjecture0_finite`. T8 with the closed-form initial condition
  (`IC`, `wolfram23_universal_ic`) is in `Smith.Universality`.
-/

import Smith.RunBounds

namespace Smith

open TM
open BiTM
open TagSystem

/-! ## The closed-form parameters of T4 -/

/-- The largest integer of the System 5 program. -/
def icB (s : System5Config) : Nat := maxInt5 s

/-- A bound on every System 5 run from `s`. -/
def icT5 (s : System5Config) : Nat := icB s * 2 ^ s.rules.length

/-- A bound on the bag elements at the end of the System 5 run. -/
def icM (s : System5Config) : Nat := icB s + icT5 s

/-- The budget of T2: the System 5 run plus the terminal phase. -/
def icH (s : System5Config) : Nat := icT5 s + icM s + 1

/-- The parameter `f` of the System 4 encoder. -/
def icF (s : System5Config) : Nat := icB s + 2 * icH s + 2 * icT5 s + 5

/-- The band of the decoder. -/
def icBand (s : System5Config) : Nat := 2 * icF s - 2 * icT5 s - 2

/-- The System 4 tape after its first set. -/
def icRest (s : System5Config) : List System4Elem :=
  starredEmptyPairs (icF s) ++ s.rules.flatMap (fun r => encodeS5RuleToS4Elems r (icF s))

/-- The length of the System 4 tape. -/
def icLen4 (s : System5Config) : Nat := (system5ToSystem4 s (icF s)).elems.length

/-- A bound on every System 4 run from the tape. -/
def icT4 (s : System5Config) : Nat := (2 * icLen4 s + 2) * (icLen4 s + 1)

/-- The fuel of T3: the System 4 run and the band. -/
def icFuel (s : System5Config) : Nat := icT4 s + icBand s

/-- The width exponent of the parity blocks. -/
def icW (s : System5Config) : Nat := icFuel s + 3 * icF s + 6

/-- The closed-form initial condition of T4 for the System 5 program `s`:
    the System 3 rendering (`initAC`) of the System 4 tape of `s`, relabeled
    to System 0 and read as a wolfram23 configuration. -/
def icStart (s : System5Config) : BiTM.Config :=
  toBi (phi2 (phi3 (initAC (icW s) (icFuel s) (encodeBag s.bag) (icRest s)).toL))

theorem system5ToSystem4_icF (s : System5Config) :
    system5ToSystem4 s (icF s) = ⟨System4Elem.set (encodeBag s.bag) :: icRest s, 0, System4State.A⟩ := rfl

theorem Inv5_ctsToSystem5 (C0 : CTS) (cfg : CTSConfig) (N : Nat) : Inv5 (ctsToSystem5 C0 cfg N) := by
  refine ⟨ctsToSystem5_bag_nodup C0 cfg N, fun e he => ctsToSystem5_bag_ge_one C0 cfg N e he, ?_⟩
  intro r hr k hk
  have := ctsToSystem5_rules_ge_three C0 cfg N r hr k hk
  omega

/-- The facts about the encoder's output that the System 4 encoder needs,
    with the closed-form parameter `icF`. -/
theorem icF_facts (C0 : CTS) (cfg : CTSConfig) (N : Nat) :
    1 ≤ icF (ctsToSystem5 C0 cfg N) ∧
    (∀ e ∈ (ctsToSystem5 C0 cfg N).bag, 1 ≤ e ∧ e < icF (ctsToSystem5 C0 cfg N)) ∧
    (∀ r ∈ (ctsToSystem5 C0 cfg N).rules, r.Nodup ∧
      ∀ k ∈ r, 0 ≤ k ∧ k + 2 * icH (ctsToSystem5 C0 cfg N) < icF (ctsToSystem5 C0 cfg N)) := by
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = ctsToSystem5 C0 cfg N := ⟨_, rfl⟩
  rw [← hs0]
  have hinv0 : Inv5 s0 := hs0 ▸ Inv5_ctsToSystem5 C0 cfg N
  have hbound0 : Bound5 s0 (icB s0 : Int) := Bound5_maxInt5 s0
  have hf : icF s0 = icB s0 + 2 * icH s0 + 2 * icT5 s0 + 5 := rfl
  refine ⟨by omega, fun e he => ?_, fun r hr => ⟨ctsToSystem5_rules_nodup C0 cfg N r (hs0 ▸ hr), fun k hk => ?_⟩⟩
  · have h1 := hinv0.2.1 e he
    have h2 := hbound0.1 e he
    constructor <;> omega
  · have h1 := hinv0.2.2 r hr k hk
    have h2 := hbound0.2 r hr k hk
    constructor <;> omega

/-! ## The System 4 emulation of a cyclic tag run

The System 4 side of T4, shared by the finite form and by the infinite form
of `Smith.Infinite`: with the closed-form parameter `icF`, the encoder tape
runs, at strictly increasing times, through configurations whose head has
just turned at the left end (on the first set in state B, a star after the
leading conglomerate), which decode below the band `icBand` to the cyclic
tag configurations, and then exits in state C, within `icT4` steps. -/

theorem system4_emulation (C0 : CTS) (cfg : CTSConfig) (N : Nat) (c' : CTSConfig)
    (hrun : C0.nSteps cfg (C0.appendants.length * N) = some c') (hne : c'.data ≠ []) :
    ∃ (T4 : Nat) (cE : System4Config) (times : Nat → Nat),
      T4 ≤ icT4 (ctsToSystem5 C0 cfg N) ∧
      System4.nSteps (system5ToSystem4 (ctsToSystem5 C0 cfg N) (icF (ctsToSystem5 C0 cfg N))) T4
        = some cE ∧
      cE.state = System4State.C ∧ cE.active = cE.elems.length ∧
      (∀ i, i < C0.appendants.length * N → times i < times (i + 1)) ∧
      (∀ i, i ≤ C0.appendants.length * N → times i + 1 ≤ T4 ∧
        ∃ ci K R, C0.nSteps cfg i = some ci ∧ K ≠ [] ∧
          System4.nSteps (system5ToSystem4 (ctsToSystem5 C0 cfg N) (icF (ctsToSystem5 C0 cfg N)))
            (times i + 1) = some ⟨sets K ++ System4Elem.star :: R, 0, System4State.B⟩ ∧
          (decodeS4 ⟨sets K ++ System4Elem.star :: R, 0, System4State.B⟩
            (icBand (ctsToSystem5 C0 cfg N))).bind decodeBag = some (dbl ci.data)) := by
  obtain ⟨hf1, hbag1, hrules0⟩ := icF_facts C0 cfg N
  obtain ⟨n, hn⟩ : ∃ n, n = C0.appendants.length * N := ⟨_, rfl⟩
  rw [← hn] at hrun ⊢
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = ctsToSystem5 C0 cfg N := ⟨_, rfl⟩
  rw [← hs0] at hbag1 hrules0 hf1 ⊢
  obtain ⟨t5, h50, h5mono, h5tr⟩ := conjecture5_finite_exact C0 cfg N n (le_of_eq hn) c' hrun
  rw [← hs0] at h5tr
  obtain ⟨cn, sn, hcn, hsn, hrep5n, hlenn⟩ := h5tr n (le_refl n)
  rw [hrun] at hcn
  obtain rfl := Option.some.inj hcn
  have hrules_n : sn.rules = [] := by
    have h0 : sn.rules.length = 0 := by rw [hlenn, ← hn]; simp
    exact List.length_eq_zero_iff.mp h0
  have hinv0 : Inv5 s0 := hs0 ▸ Inv5_ctsToSystem5 C0 cfg N
  obtain ⟨B0, hB0⟩ : ∃ B0, B0 = icB s0 := ⟨_, rfl⟩
  have hbound0 : Bound5 s0 (B0 : Int) := by rw [hB0]; exact Bound5_maxInt5 s0
  obtain ⟨T5, hT5⟩ : ∃ T5, T5 = icT5 s0 := ⟨_, rfl⟩
  have ht5n : t5 n ≤ T5 := by
    rw [hT5, icT5, ← hB0]
    exact System5.run_bound s0 B0 hinv0 hbound0 _ _ hsn
  obtain ⟨M, hM⟩ : ∃ M, M = icM s0 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = icH s0 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = icF s0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = icBand s0 := ⟨_, rfl⟩
  have hMe : M = B0 + T5 := by rw [hM, hB0, hT5]; rfl
  have hHe : H = T5 + M + 1 := by rw [hH, hM, hT5]; rfl
  have hfe : f = B0 + 2 * H + 2 * T5 + 5 := by rw [hf, hH, hB0, hT5]; rfl
  have hbe : b = 2 * f - 2 * T5 - 2 := by rw [hb, hf, hT5]; rfl
  rw [← hf, ← hb]
  rw [← hf, ← hH] at hrules0
  rw [← hf] at hbag1
  have hboundn := Bound5_nSteps s0 B0 (t5 n) sn hbound0 hsn
  have hbagne : sn.bag ≠ [] :=
    Represents_bag_ne_nil sn (double C0) (dblCfg _) _ hrep5n (by simpa [dblCfg] using hne)
  obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil sn.bag hbagne
  obtain ⟨t4, h40, h4mono, h4tr⟩ := conjecture4_finite s0 f H (t5 n)
    hinv0.1 hbag1 hrules0 (by omega) (by omega) sn hsn
  obtain ⟨sL, c4L, hsL, hc4L, hrepL⟩ := h4tr (t5 n) (le_refl _)
  rw [hsn] at hsL
  obtain rfl := Option.some.inj hsL
  have hrepL' : RepS4 c4L sn f (t5 n) ((T5 - t5 n + 1) + M) := by
    have : H - t5 n = (T5 - t5 n + 1) + M := by omega
    rw [this] at hrepL; exact hrepL
  have he0le : e0 ≤ (M : Int) + 1 := by
    have := hboundn.1 e0 he0
    omega
  obtain ⟨k, cE, hrunE, hstE, hactE, hnoneE⟩ :=
    repS4_terminal M c4L sn f (t5 n) (T5 - t5 n + 1) hrepL' hrules_n ⟨e0, he0, he0le⟩
  obtain ⟨K, hKne, -, hc4Leq, -⟩ := hrepL
  have hk1 : 1 ≤ k := by
    cases k with
    | zero =>
      rw [System4.nSteps_zero] at hrunE
      obtain rfl := Option.some.inj hrunE
      rw [hc4Leq] at hstE
      cases hstE
    | succ k => omega
  obtain ⟨T4, hT4⟩ : ∃ T4, T4 = t4 (t5 n) + k := ⟨_, rfl⟩
  have hrunT4 : System4.nSteps (system5ToSystem4 s0 f) T4 = some cE := by
    rw [hT4, System4.nSteps_add, hc4L, Option.bind_some, hrunE]
  have hT4le : T4 ≤ icT4 s0 := by
    have := System4.run_bound _ T4 cE hrunT4
    rw [icT4, icLen4, ← hf]
    exact this
  have h4le : ∀ j, j ≤ t5 n → t4 j ≤ t4 (t5 n) := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact le_of_lt (strictMono_of_succ t4 (t5 n) h4mono j _ hlt (le_refl _))
    · exact le_refl _
  have h5le : ∀ i, i ≤ n → t5 i ≤ t5 n := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with hlt | rfl
    · exact le_of_lt (strictMono_of_succ t5 n h5mono i n hlt (le_refl _))
    · exact le_refl _
  refine ⟨T4, cE, fun i => t4 (t5 i), hT4le, hrunT4, hstE, hactE, ?_, ?_⟩
  · intro i hi
    exact strictMono_of_succ t4 (t5 n) h4mono _ _ (h5mono i hi) (h5le (i + 1) hi)
  · intro i hi
    obtain ⟨ci, si, hci, hsi, hrep5i, -⟩ := h5tr i hi
    obtain ⟨si', c4i, hsi', hc4i, hrep4i⟩ := h4tr (t5 i) (h5le i hi)
    rw [hsi] at hsi'
    obtain rfl := Option.some.inj hsi'
    have hd : t4 (t5 i) + 1 ≤ T4 := by
      have := h4le (t5 i) (h5le i hi)
      omega
    have hrep4i' := hrep4i
    obtain ⟨K, hKne, -, hc4ieq, hjh, -, -, -, -⟩ := hrep4i
    obtain ⟨K0, K', rfl⟩ := List.exists_cons_of_ne_nil hKne
    obtain ⟨g, hg⟩ : ∃ g, f - 2 * t5 i = g + 1 := ⟨f - 2 * t5 i - 1, by omega⟩
    have hE : sets (K0 :: K') ++ starredEmptyPairs (f - 2 * t5 i) ++ encBlocks si.rules f (2 * t5 i)
        = sets (K0 :: K') ++ System4Elem.star ::
            (System4Elem.set [] :: (starredEmptyPairs g ++ encBlocks si.rules f (2 * t5 i))) := by
      rw [hg, starredEmptyPairs_succ]
      simp only [List.append_assoc, List.cons_append]
    have hcd' : System4.nSteps (system5ToSystem4 s0 f) (t4 (t5 i) + 1)
        = some ⟨sets (K0 :: K') ++ System4Elem.star ::
            (System4Elem.set [] :: (starredEmptyPairs g ++ encBlocks si.rules f (2 * t5 i))), 0,
            System4State.B⟩ := by
      rw [System4.nSteps_add, hc4i, Option.bind_some, System4.nSteps_one, hc4ieq, hE]
      show System4.step ⟨System4Elem.set K0 :: (sets K' ++ System4Elem.star ::
        (System4Elem.set [] :: (starredEmptyPairs g ++ encBlocks si.rules f (2 * t5 i)))), 0,
        System4State.A⟩ = _
      rw [step_setA_zero]
      rfl
    refine ⟨hd, ci, K0 :: K', _, hci, by simp, hcd', ?_⟩
    rw [decodeS4_state _ _ _ System4State.A, ← hE, ← hc4ieq]
    have hbagb : ∀ e ∈ si.bag, 2 * e - 2 < b := by
      intro e he
      have h1 := (Bound5_nSteps s0 B0 (t5 i) si hbound0 hsi).1 e he
      have h2 := h5le i hi
      omega
    obtain ⟨l, hl, hlperm⟩ := RepS4_decode_band c4i si f (t5 i) (H - t5 i) hrep4i' b
      (by have := h5le i hi; omega) hbagb
    rw [hl, Option.bind_some]
    obtain ⟨⟨a, hasc, hperm⟩, -⟩ := hrep5i
    exact decodeBag_of_perm l _ a hasc (hlperm.trans hperm)

/-! ## T4 with the closed-form initial condition -/

/-- T4 (Smith's Conjecture 0 in finite form) with the initial condition,
    the block width and the band given in closed form by the System 5
    program `ctsToSystem5 C0 cfg N`, which is itself a closed form of the
    cyclic tag system, its configuration and the budget `N`. For a cyclic
    tag run that lasts the `appendants.length * N` steps of the budget and
    leaves a nonempty word: wolfram23 from `icStart` is valid and in state
    A; at strictly increasing times `times i` its tape decodes, by
    `decodeW23` with the width `2 ^ icW` and the band `icBand`, to the
    doubled working string of the `i`-th cyclic tag configuration; up to
    the exit time `T` the run stays on the explicit tape; at time `T + 1`
    the head is on the cell right of the tape, a 0, in state A. -/
theorem conjecture0_closed (C0 : CTS) (cfg : CTSConfig) (N : Nat) (c' : CTSConfig)
    (hrun : C0.nSteps cfg (C0.appendants.length * N) = some c') (hne : c'.data ≠ []) :
    ∃ (times : Nat → Nat) (T : Nat),
      IsValidWolfram23Cfg (icStart (ctsToSystem5 C0 cfg N)) ∧
      (icStart (ctsToSystem5 C0 cfg N)).state = 1 ∧
      (∀ i, i < C0.appendants.length * N → times i < times (i + 1)) ∧
      (∀ i, i ≤ C0.appendants.length * N → times i ≤ T ∧
        ∃ ci cfgi, C0.nSteps cfg i = some ci ∧
          BiTM.nSteps wolfram23 (icStart (ctsToSystem5 C0 cfg N)) (times i) = some cfgi ∧
          decodeW23 (2 ^ icW (ctsToSystem5 C0 cfg N)) (icBand (ctsToSystem5 C0 cfg N)) cfgi
            = some (dbl ci.data)) ∧
      (∀ τ, τ ≤ T → ∃ cfgτ, BiTM.nSteps wolfram23 (icStart (ctsToSystem5 C0 cfg N)) τ = some cfgτ ∧
        biSize cfgτ = biSize (icStart (ctsToSystem5 C0 cfg N))) ∧
      (∃ L : List Nat, BiTM.nSteps wolfram23 (icStart (ctsToSystem5 C0 cfg N)) (T + 1)
        = some ⟨1, L, 0, []⟩ ∧ L.length = biSize (icStart (ctsToSystem5 C0 cfg N))) := by
  obtain ⟨T4, cE, t4, hT4le, hrunT4, hstE, hactE, h4mono, h4tr⟩ := system4_emulation C0 cfg N c' hrun hne
  obtain ⟨hf1, hbag1, hrules0⟩ := icF_facts C0 cfg N
  obtain ⟨n, hn⟩ : ∃ n, n = C0.appendants.length * N := ⟨_, rfl⟩
  rw [← hn] at h4mono h4tr ⊢
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = ctsToSystem5 C0 cfg N := ⟨_, rfl⟩
  rw [← hs0] at hT4le hrunT4 h4tr hf1 hbag1 hrules0 ⊢
  obtain ⟨f, hf⟩ : ∃ f, f = icF s0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = icBand s0 := ⟨_, rfl⟩
  obtain ⟨h4, hh4⟩ : ∃ h4, h4 = icFuel s0 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = icW s0 := ⟨_, rfl⟩
  rw [← hf] at hrunT4 h4tr hf1 hbag1 hrules0
  rw [← hb] at h4tr
  have hh4e : h4 = icT4 s0 + b := by rw [hh4, hb]; rfl
  have hwe : w = h4 + 3 * f + 6 := by rw [hw, hh4, hf]; rfl
  have hw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hN3 : h4 + 3 ≤ 2 ^ w := by omega
  have h3f : 3 * f + 3 ≤ 2 ^ w := by omega
  have hrules0' : ∀ r ∈ s0.rules, ∀ k ∈ r, 0 ≤ k ∧ k < f := by
    intro r hr k hk
    have := (hrules0 r hr).2 k hk
    constructor <;> omega
  have hc40 : system5ToSystem4 s0 f = ⟨System4Elem.set (encodeBag s0.bag) :: icRest s0, 0,
      System4State.A⟩ := by rw [hf]; rfl
  have hwf := system5ToSystem4_wellFormed s0 f hf1
  have hlast := system5ToSystem4_last_set s0 f hf1
  have hbnd : ∀ S, System4Elem.set S ∈ System4Elem.set (encodeBag s0.bag) :: icRest s0 →
      ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w := by
    intro S hS e he
    have := system5ToSystem4_elem_lt s0 f hbag1 hrules0' S (by rw [hc40]; exact hS) e he
    constructor <;> omega
  rw [hc40] at hwf hlast hrunT4 h4tr
  obtain ⟨times0, h00, h0mono, h0tr⟩ := conjecture3_finite w h4 T4 (encodeBag s0.bag) _ hN3 hwf
    hlast hbnd (by omega) cE hrunT4
  obtain ⟨start3, hstart3⟩ : ∃ c, c = phi2 (phi3 (initAC w h4 (encodeBag s0.bag) (icRest s0)).toL) :=
    ⟨_, rfl⟩
  have hstart : icStart s0 = toBi start3 := by rw [hstart3, hw, hh4]; rfl
  rw [hstart]
  rw [← hstart3] at h0tr
  have hst3 : start3.state ≠ LState.C := by rw [hstart3]; exact phi2_state_ne_C _
  have hstart_state : (toBi start3).state = 1 := by rw [hstart3]; rfl
  obtain ⟨cT, c3T, hcT, hrun0T, hrep3T⟩ := h0tr T4 (le_refl _)
  rw [hrunT4] at hcT
  obtain rfl := Option.some.inj hcT
  obtain ⟨L3, rfl⟩ := rep3_exit c3T cE w _ hrep3T hactE hstE
  have h0le : ∀ j, j ≤ T4 → times0 j ≤ times0 T4 := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact le_of_lt (strictMono_of_succ times0 T4 h0mono j T4 hlt (le_refl _))
    · exact le_refl _
  have h4le : ∀ i, i ≤ n → t4 i + 1 ≤ T4 := fun i hi => (h4tr i hi).1
  rw [← hw, ← hb]
  refine ⟨fun i => times0 (t4 i + 1), times0 T4,
    toBi_valid start3 hst3, hstart_state, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact strictMono_of_succ times0 T4 h0mono _ _ (by have := h4mono i hi; omega) (h4le (i + 1) hi)
  · intro i hi
    obtain ⟨hd, ci, K, R, hci, hK, hc4i, hdec⟩ := h4tr i hi
    obtain ⟨cd, c3d, hcd, hrun0d, hrep3d⟩ := h0tr (t4 i + 1) hd
    rw [hc4i] at hcd
    obtain rfl := Option.some.inj hcd
    refine ⟨h0le _ hd, ci, toBi (phi2 (phi3 c3d)), hci, (toBi_run start3 hst3 _ _ hrun0d).1, ?_⟩
    rw [rep3_decode_zero c3d K R w _ b hK (by omega) _ hrep3d, hdec]
  · intro τ hτ
    obtain ⟨cτ, hcτ⟩ := StepSys.nSteps_some_of_le (lsys sys0) start3 _ (times0 T4) τ hτ hrun0T
    refine ⟨toBi cτ, (toBi_run start3 hst3 τ cτ hcτ).1, ?_⟩
    rw [biSize_toBi, biSize_toBi, lnSteps_length sys0 start3 τ cτ hcτ]
  · refine ⟨0 :: (L3.map sw).map Fin.val, ?_, ?_⟩
    · rw [biNSteps_add, (toBi_run start3 hst3 _ _ hrun0T).1, Option.bind_some, biNSteps_one, phi_exit]
      exact wolfram23_exit_step _
    · rw [biSize_toBi, ← lnSteps_length sys0 start3 _ _ hrun0T, phi_exit]
      simp [LConfig.toList]

/-- T4 with an existential initial condition: the form of the statement
    before the closed form, a corollary of `conjecture0_closed`. -/
theorem conjecture0_finite (C0 : CTS) (cfg : CTSConfig) (N : Nat) (c' : CTSConfig)
    (hrun : C0.nSteps cfg (C0.appendants.length * N) = some c') (hne : c'.data ≠ []) :
    ∃ (start : BiTM.Config) (w b : Nat) (times : Nat → Nat) (T : Nat),
      IsValidWolfram23Cfg start ∧ start.state = 1 ∧
      (∀ i, i < C0.appendants.length * N → times i < times (i + 1)) ∧
      (∀ i, i ≤ C0.appendants.length * N → times i ≤ T ∧
        ∃ ci cfgi, C0.nSteps cfg i = some ci ∧ BiTM.nSteps wolfram23 start (times i) = some cfgi ∧
          decodeW23 (2 ^ w) b cfgi = some (dbl ci.data)) ∧
      (∀ τ, τ ≤ T → ∃ cfgτ, BiTM.nSteps wolfram23 start τ = some cfgτ ∧ biSize cfgτ = biSize start) ∧
      (∃ L : List Nat, BiTM.nSteps wolfram23 start (T + 1) = some ⟨1, L, 0, []⟩ ∧
        L.length = biSize start) := by
  obtain ⟨times, T, h1, h2, h3, h4, h5, h6⟩ := conjecture0_closed C0 cfg N c' hrun hne
  exact ⟨_, _, _, times, T, h1, h2, h3, h4, h5, h6⟩

end Smith
