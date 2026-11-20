/-
  TagSystem.RawRuns

  The raw runs of a binary machine through its Cocke-Minsky tag system. The
  round lemmas `round1` to `round5` are stated at the level of the tag
  system, for any state `q`; only `tm_step_tag` needs `q != 0`, to unfold
  `BiTM.step`, which is `none` in the halting state 0. The raw step
  `rawStep` is the step of the machine with state 0 treated as an ordinary
  state (row 0 of the table, which `WF` keeps in range), and the tag system
  carries it out in `roundLen` tag steps (`raw_step_tag`) whatever the
  state. So the tag run from the word of a valid configuration is defined
  for every number of steps (`tag_run_total`), and at time `tagTime c n`
  it is the word of the `n`-th raw configuration (`tag_rawRun`), which is
  the `n`-th configuration of the machine as long as the machine runs
  (`rawRun_eq`). T6 emulates raw runs, so that block `k` reproduces `k`
  steps whether or not the machine halts first.

  Contents: `rawStep`, `step_eq_rawStep`, `rawStep_valid`, `roundLen`,
  `raw_step_tag`, `rawRun`, `tagTime`, `rawRun_eq`, `tag_rawRun`,
  `tagTime_succ`, `tagTime_strictMono`, `tagTime_mono`, `le_tagTime`,
  `tag_run_total`.
-/

import TagSystem.TMToCTS

namespace TagSystem

open TM
open BiTM

variable (tm : Machine)

/-- The step of the machine with the halting state treated as an ordinary
    state: the one `BiTM.step` takes in every other state. -/
def rawStep (c : Config) : Config :=
  match (tm.transition c.state c.head).dir with
  | Dir.L => ⟨(tm.transition c.state c.head).nextState, (readHead c.left).2,
      (readHead c.left).1, (tm.transition c.state c.head).write :: c.right⟩
  | Dir.R => ⟨(tm.transition c.state c.head).nextState,
      (tm.transition c.state c.head).write :: c.left, (readHead c.right).1, (readHead c.right).2⟩

theorem step_eq_rawStep (c : Config) (hq : c.state ≠ 0) : BiTM.step tm c = some (rawStep tm c) := by
  obtain ⟨q, left, head, right⟩ := c
  simp only at hq
  cases hd : (tm.transition q head).dir with
  | R => rw [step_R tm q left head right hq hd]; simp [rawStep, hd]
  | L => rw [step_L tm q left head right hq hd]; simp [rawStep, hd]

theorem rawStep_valid (hwf : WF tm) (c : Config) (hv : ValidCfg c) (hst : c.state < tm.numStates) :
    ValidCfg (rawStep tm c) ∧ (rawStep tm c).state < tm.numStates := by
  obtain ⟨q, left, head, right⟩ := c
  obtain ⟨hh, hl, hr⟩ := hv
  simp only at hh hl hr hst
  have hw := (hwf q hst head hh).1
  have hn := (hwf q hst head hh).2
  cases hd : (tm.transition q head).dir with
  | R =>
    simp only [rawStep, hd]
    refine ⟨⟨readHead_fst_lt right hr, ?_, readHead_snd_lt right hr⟩, hn⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hw
    · exact hl a ha
  | L =>
    simp only [rawStep, hd]
    refine ⟨⟨readHead_fst_lt left hl, readHead_snd_lt left hl, ?_⟩, hn⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hw
    · exact hr a ha

/-- The number of tag steps of the round that carries out a raw step: three
    rounds for a move to the right, five for a move to the left, in the
    halves `m = val left` and `N = head + 2 val right` of the word. -/
def roundLen (c : Config) : Nat :=
  match (tm.transition c.state c.head).dir with
  | Dir.R =>
    (val c.left + (c.head + 2 * val c.right) + 2) + (val c.left + (c.head + 2 * val c.right) / 2 + 2) +
      (val c.left + (c.head + 2 * val c.right) / 2 + 2)
  | Dir.L =>
    (val c.left + (c.head + 2 * val c.right) + 2) + (val c.left + (c.head + 2 * val c.right) / 2 + 2) +
      (val c.left + (c.head + 2 * val c.right) / 2 + 2) +
      (val c.left / 2 + 2 * ((c.head + 2 * val c.right) / 2) + 2) +
      (val c.left / 2 + 2 * ((c.head + 2 * val c.right) / 2) + 2)

theorem roundLen_pos (c : Config) : 1 ≤ roundLen tm c := by
  unfold roundLen
  cases (tm.transition c.state c.head).dir <;> simp only <;> omega

/-- The tag system carries out a raw step in `roundLen` steps, in every
    state (`tm_step_tag` without `q != 0`). -/
theorem raw_step_tag (c : Config) (hv : ValidCfg c) (hb : (tm.transition c.state c.head).write < 2) :
    nStepsP (prod tm) (word c) (roundLen tm c) = some (word (rawStep tm c)) := by
  obtain ⟨q, left, head, right⟩ := c
  obtain ⟨hh, hl, hr⟩ := hv
  simp only at hh hl hr hb
  have hbit : bit (decide (head = 1)) = head := bit_decide_head head hh
  have hnxt : nxt tm q (decide (head = 1)) = (tm.transition q head).nextState := by
    simp [nxt, hbit]
  have hwr : wr tm q (decide (head = 1)) = (tm.transition q head).write := by
    simp only [wr, hbit]
    exact Nat.mod_eq_of_lt hb
  have hdr : dr tm q (decide (head = 1)) = (tm.transition q head).dir := by
    simp [dr, hbit]
  have hpar : decide ((head + 2 * val right) % 2 = 1) = decide (head = 1) := by
    rw [decide_eq_decide]; omega
  have hhalf : (head + 2 * val right) / 2 = val right := by omega
  cases hd : (tm.transition q head).dir with
  | R =>
    simp only [roundLen, rawStep, hd]
    simp only [word, val_cons, val_readHead]
    rw [nStepsP_add, nStepsP_add, round1, Option.bind_some, round2, Option.bind_some, hpar,
      hhalf, round3R tm q _ _ _ (by rw [hdr, hd]), hnxt, hwr]
  | L =>
    simp only [roundLen, rawStep, hd]
    simp only [word, val_cons, readHead_fst left hl, val_readHead_snd left hl]
    rw [nStepsP_add, nStepsP_add, nStepsP_add, nStepsP_add, round1, Option.bind_some,
      round2, Option.bind_some, hpar, hhalf, round3L tm q _ _ _ (by rw [hdr, hd]), Option.bind_some,
      round4, Option.bind_some, round5, hnxt, hwr, bit_decide_mod]
    have e : 2 * (tm.transition q head).write + val left % 2 + 4 * val right
        = val left % 2 + 2 * ((tm.transition q head).write + 2 * val right) := by omega
    rw [e]

/-- The raw run. -/
def rawRun (c : Config) : Nat → Config
  | 0 => c
  | n + 1 => rawRun (rawStep tm c) n

/-- The tag time of `n` raw steps: the sum of their round lengths. -/
def tagTime (c : Config) : Nat → Nat
  | 0 => 0
  | n + 1 => roundLen tm c + tagTime (rawStep tm c) n

theorem tagTime_succ (c : Config) (n : Nat) :
    tagTime tm c (n + 1) = tagTime tm c n + roundLen tm (rawRun tm c n) := by
  induction n generalizing c with
  | zero => simp [tagTime, rawRun]
  | succ n ih =>
    show roundLen tm c + tagTime tm (rawStep tm c) (n + 1) = _
    rw [ih (rawStep tm c)]
    show _ = roundLen tm c + tagTime tm (rawStep tm c) n + roundLen tm (rawRun tm (rawStep tm c) n)
    omega

theorem tagTime_strictMono (c : Config) (i j : Nat) (h : i < j) : tagTime tm c i < tagTime tm c j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [tagTime_succ]
    have := roundLen_pos tm (rawRun tm c j)
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with hlt | rfl
    · have := ih hlt; omega
    · omega

theorem tagTime_mono (c : Config) (i j : Nat) (h : i ≤ j) : tagTime tm c i ≤ tagTime tm c j := by
  rcases Nat.lt_or_eq_of_le h with hlt | rfl
  · exact le_of_lt (tagTime_strictMono tm c i j hlt)
  · exact le_refl _

theorem le_tagTime (c : Config) (n : Nat) : n ≤ tagTime tm c n := by
  induction n generalizing c with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    show n + 1 ≤ roundLen tm c + tagTime tm (rawStep tm c) n
    have := roundLen_pos tm c
    have := ih (rawStep tm c)
    omega

/-- The raw run agrees with the machine's run as long as the machine runs. -/
theorem rawRun_eq (c : Config) (n : Nat) (c' : Config) (h : BiTM.nSteps tm c n = some c') :
    rawRun tm c n = c' := by
  induction n generalizing c with
  | zero =>
    simp only [BiTM.nSteps, Option.some.injEq] at h
    exact h
  | succ n ih =>
    have hq : c.state ≠ 0 := by
      intro h0
      obtain ⟨q, l, a, r⟩ := c
      simp only at h0
      subst h0
      simp [BiTM.nSteps, BiTM.step] at h
    have h' : BiTM.nSteps tm (rawStep tm c) n = some c' := by
      simp only [BiTM.nSteps, step_eq_rawStep tm c hq] at h
      exact h
    exact ih (rawStep tm c) h'

theorem rawRun_valid (hwf : WF tm) (c : Config) (hv : ValidCfg c) (hst : c.state < tm.numStates)
    (n : Nat) : ValidCfg (rawRun tm c n) ∧ (rawRun tm c n).state < tm.numStates := by
  induction n generalizing c with
  | zero => exact ⟨hv, hst⟩
  | succ n ih =>
    obtain ⟨hv1, hst1⟩ := rawStep_valid tm hwf c hv hst
    exact ih (rawStep tm c) hv1 hst1

/-- At tag time `tagTime c n` the tag run is at the word of the `n`-th raw
    configuration. -/
theorem tag_rawRun (hwf : WF tm) (c : Config) (hv : ValidCfg c) (hst : c.state < tm.numStates)
    (n : Nat) : nStepsP (prod tm) (word c) (tagTime tm c n) = some (word (rawRun tm c n)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hv1, hst1⟩ := rawStep_valid tm hwf c hv hst
    show nStepsP (prod tm) (word c) (roundLen tm c + tagTime tm (rawStep tm c) n) = _
    rw [nStepsP_add, raw_step_tag tm c hv (hwf c.state hst c.head hv.1).1, Option.bind_some]
    exact ih (rawStep tm c) hv1 hst1

theorem nStepsP_some_of_le (P : Sym → List Sym) (w : List Sym) (a b : Nat) (hab : a ≤ b)
    (w' : List Sym) (h : nStepsP P w b = some w') : ∃ w'', nStepsP P w a = some w'' := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  rw [nStepsP_add] at h
  cases ha : nStepsP P w a with
  | none => rw [ha] at h; cases h
  | some w'' => exact ⟨w'', rfl⟩

/-- The tag run from the word of a valid configuration is defined for every
    number of steps. -/
theorem tag_run_total (hwf : WF tm) (c : Config) (hv : ValidCfg c) (hst : c.state < tm.numStates)
    (t : Nat) : ∃ w, nStepsP (prod tm) (word c) t = some w :=
  nStepsP_some_of_le _ _ t (tagTime tm c t) (le_tagTime tm c t) _ (tag_rawRun tm hwf c hv hst t)

end TagSystem
