/-
  Smith.Infinite

  PLAN.md target T6 (milestone M7): the infinite form of Conjecture 0
  (TM23Proof.pdf p. 21-22, "From arbitrary to infinite"). One right-infinite
  tape, built once from the machine and its input, on which wolfram23
  emulates the machine forever: the tape is the concatenation of blocks, the
  `k`-th of which emulates the first `k` steps; the blocks run one after the
  other, each handing over to the next through System 4's rule 5.

  The block: Smith's finite initial condition turns the head round at the
  left end with `0^m 2 2 1^t`, which cannot be chained (p. 25-26). Here each
  block is, in System 4 terms, a leading star, `r - 1` guard sets `{1, n}`
  separated by stars, the guard `{0, 1, n - 1}`, and the encoder tape of the
  program (`Smith.Guards`). The head enters the block on its leading star in
  state C, which is exactly where the previous block's run leaves it: the
  scan of the previous block's last set exits in state C onto the 0 that
  stands for the first cell of the next block's first guard. The entry
  traverses the guards and arrives on the program's first set in state B;
  the program's turns at its left end consume one guard each; the run of
  the program ends with the exit in state C onto the next block's leading
  star.

  The System 3 side is the relation `Rep3` of `Smith.Conjecture3` with a junk
  left end (the tape before the block, never visited, `SafeC`) and a
  closing `0` followed by the next block (`Closing.zero`). The wolfram23 run
  on the infinite tape is the run on any finite prefix as long as that run
  stays on the prefix (`Agree`, `agree_run`), which the System 3 zipper
  guarantees for as many blocks as one likes. Block `k` emulates the longest
  run of at most `k` steps, so the theorem needs no hypothesis on halting:
  a halting machine's run is reproduced in full by every block from some
  point on.

  Contents: `IConfig`, `istep`, `inSteps`, `Agree`, `agree_run`, `truncI`,
  `decodeTM_trunc`, `rep3_exit_zero`, `blockTape`, `blockAC`, `blockAC_OK`,
  `block_run`, `BlockData`, `BlockSpec`, `block_exists`, `entry3`,
  `block_sys3`, `segCells`, `chain_sys3`, `start3`, `startFin`, `stage_w23`,
  `tape`, `istart`, `IValid`, `inSteps_valid`, `wolfram23_infinite`.
-/

import Smith.Universality
import Smith.Guards

namespace Smith

open TM
open BiTM
open LState
open TagSystem

/-! ## A right-infinite tape -/

/-- A wolfram23 configuration whose tape is infinite to the right: the cells
    left of the head nearest first (blank beyond, as in `BiTM.Config`), the
    head cell, and the cells right of the head as a stream. -/
structure IConfig where
  state : Nat
  left : List Nat
  head : Nat
  right : Nat → Nat

/-- One step, as `BiTM.step`. -/
def istep (tm : Machine) (c : IConfig) : Option IConfig :=
  if c.state == 0 then none
  else
    let r := tm.transition c.state c.head
    match r.dir with
    | Dir.L =>
      let p := readHead c.left
      some ⟨r.nextState, p.2, p.1, fun i => if i = 0 then r.write else c.right (i - 1)⟩
    | Dir.R =>
      some ⟨r.nextState, r.write :: c.left, c.right 0, fun i => c.right (i + 1)⟩

/-- `n` steps. -/
def inSteps (tm : Machine) (c : IConfig) : Nat → Option IConfig
  | 0 => some c
  | n + 1 =>
    match istep tm c with
    | none => none
    | some c' => inSteps tm c' n

@[simp] theorem inSteps_zero (tm : Machine) (c : IConfig) : inSteps tm c 0 = some c := rfl

theorem inSteps_succ (tm : Machine) (c : IConfig) (n : Nat) :
    inSteps tm c (n + 1) = (istep tm c).bind fun c' => inSteps tm c' n := by
  show (match istep tm c with | none => none | some c' => inSteps tm c' n) = _
  cases istep tm c <;> rfl

/-- The finite configuration `c` agrees with the infinite one `d` on the
    state, the left tape, the head and the explicit cells right of the head. -/
def Agree (c : BiTM.Config) (d : IConfig) : Prop :=
  c.state = d.state ∧ c.left = d.left ∧ c.head = d.head ∧
    ∀ i, i < c.right.length → c.right[i]? = some (d.right i)

/-- The first `W` cells right of the head, as a finite configuration. -/
def truncI (W : Nat) (d : IConfig) : BiTM.Config :=
  ⟨d.state, d.left, d.head, (List.range W).map d.right⟩

theorem truncI_agree (W : Nat) (d : IConfig) : Agree (truncI W d) d := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  simp only [truncI, List.length_map, List.length_range] at hi
  simp [truncI, hi]

/-- A step that does not read the blank right of the finite tape is matched
    by the infinite tape. -/
theorem agree_step (tm : Machine) (c : BiTM.Config) (d : IConfig) (h : Agree c d)
    (c' : BiTM.Config) (hs : BiTM.step tm c = some c') (hsz : biSize c' = biSize c) :
    ∃ d', istep tm d = some d' ∧ Agree c' d' := by
  obtain ⟨hst, hl, hh, hr⟩ := h
  obtain ⟨s, L, a, R⟩ := c
  obtain ⟨s', L', a', R'⟩ := d
  simp only at hst hl hh hr
  subst hst hl hh
  unfold BiTM.step at hs
  unfold istep
  by_cases h0 : s = 0
  · subst h0; simp at hs
  simp only [beq_iff_eq, h0, if_false] at hs ⊢
  cases hd : (tm.transition s a).dir with
  | L =>
    rw [hd] at hs
    simp only at hs
    obtain rfl := Option.some.inj hs
    refine ⟨_, rfl, rfl, rfl, rfl, ?_⟩
    intro i hi
    cases i with
    | zero => simp
    | succ j =>
      simp only [List.length_cons] at hi
      simp only [List.getElem?_cons_succ, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      exact hr j (by omega)
  | R =>
    rw [hd] at hs
    simp only at hs
    cases R with
    | nil =>
      exfalso
      obtain rfl := Option.some.inj hs
      simp [biSize, readHead] at hsz
    | cons x xs =>
      obtain rfl := Option.some.inj hs
      have h0' := hr 0 (by simp)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0'
      simp only [readHead]
      refine ⟨_, rfl, rfl, rfl, h0', ?_⟩
      intro i hi
      have := hr (i + 1) (by simp; omega)
      simpa using this

theorem biNSteps_succ' (tm : Machine) (cfg : BiTM.Config) (n : Nat) :
    BiTM.nSteps tm cfg (n + 1) = (BiTM.step tm cfg).bind fun c => BiTM.nSteps tm c n := by
  show (match BiTM.step tm cfg with | none => none | some c => BiTM.nSteps tm c n) = _
  cases BiTM.step tm cfg <;> rfl

/-- A run that stays on the finite tape is matched by the infinite tape. -/
theorem agree_run (tm : Machine) (n : Nat) : ∀ (c : BiTM.Config) (d : IConfig), Agree c d →
    (∀ τ, τ ≤ n → ∀ cτ, BiTM.nSteps tm c τ = some cτ → biSize cτ = biSize c) →
    ∀ cn, BiTM.nSteps tm c n = some cn → ∃ dn, inSteps tm d n = some dn ∧ Agree cn dn := by
  induction n with
  | zero =>
    intro c d h _ cn hcn
    simp only [BiTM.nSteps, Option.some.injEq] at hcn
    subst hcn
    exact ⟨d, rfl, h⟩
  | succ n ih =>
    intro c d h hsz cn hcn
    rw [biNSteps_succ'] at hcn
    cases hs : BiTM.step tm c with
    | none => rw [hs] at hcn; cases hcn
    | some c1 =>
      rw [hs, Option.bind_some] at hcn
      have h1 : biSize c1 = biSize c := hsz 1 (by omega) c1 (by rw [biNSteps_succ', hs]; rfl)
      obtain ⟨d1, hd1, hag1⟩ := agree_step tm c d h c1 hs h1
      have hsz' : ∀ τ, τ ≤ n → ∀ cτ, BiTM.nSteps tm c1 τ = some cτ → biSize cτ = biSize c1 := by
        intro τ hτ cτ hcτ
        rw [h1]
        exact hsz (τ + 1) (by omega) cτ (by rw [biNSteps_succ', hs, Option.bind_some]; exact hcτ)
      obtain ⟨dn, hdn, hagn⟩ := ih c1 d1 hag1 hsz' cn hcn
      exact ⟨dn, by rw [inSteps_succ, hd1, Option.bind_some]; exact hdn, hagn⟩

/-! ## The decoder on a window -/

theorem takeWhile_append_of_mem_zero (R R' : List Nat) (hz : 0 ∈ R) :
    (R ++ R').takeWhile (fun c => c != 0) = R.takeWhile (fun c => c != 0) := by
  induction R with
  | nil => simp at hz
  | cons x xs ih =>
    by_cases hx : x = 0
    · subst hx; simp
    · have hx' : (x != 0) = true := by simpa using hx
      rw [List.cons_append, List.takeWhile_cons, hx', List.takeWhile_cons, hx']
      simp only [ite_true]
      have hz' : 0 ∈ xs := by
        rcases List.mem_cons.mp hz with h | h
        · exact absurd h.symm hx
        · exact h
      rw [ih hz']

/-- The decoder reads only up to the first 0 right of the head. -/
theorem decodeW23_append (N b : Nat) (s : Nat) (L : List Nat) (a : Nat) (R R' : List Nat)
    (hz : 0 ∈ R) : decodeW23 N b ⟨s, L, a, R ++ R'⟩ = decodeW23 N b ⟨s, L, a, R⟩ := by
  unfold decodeW23
  simp only
  rw [takeWhile_append_of_mem_zero R R' hz]

/-- On the infinite tape, a window that reaches the first 0 right of the
    head decodes as the finite configuration does. -/
theorem decodeTM_trunc (S N b W : Nat) (c : BiTM.Config) (d : IConfig) (h : Agree c d)
    (hW : c.right.length ≤ W) (hz : 0 ∈ c.right) :
    decodeTM S N b (truncI W d) = decodeTM S N b c := by
  obtain ⟨hst, hl, hh, hr⟩ := h
  have hR : (List.range W).map d.right
      = c.right ++ (List.range (W - c.right.length)).map (fun i => d.right (c.right.length + i)) := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < c.right.length
    · rw [List.getElem?_append_left hi, List.getElem?_map, List.getElem?_range (by omega)]
      simp only [Option.map_some]
      exact (hr i hi).symm
    · rw [List.getElem?_append_right (by omega), List.getElem?_map, List.getElem?_map]
      by_cases hiW : i < W
      · rw [List.getElem?_range hiW, List.getElem?_range (by omega)]
        simp only [Option.map_some]
        congr 2
        omega
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
        rfl
  unfold decodeTM
  obtain ⟨s, L, a, R⟩ := c
  simp only at hst hl hh hr hR hz hW
  simp only [truncI, hR, hst, hl, hh]
  rw [← hst, ← hl, ← hh, decodeW23_append N b s L a R _ hz]

/-! ## The exit onto the next block -/

/-- At System 4's exit in state C with a closing `0`, the System 3 head is on
    that 0 in state A, with a 0 to its left: the next block's entry shape. -/
theorem rep3_exit_zero (Rc : List (Fin 3)) (c3 : LConfig) (c4 : System4Config) (w h : Nat)
    (hrep : Rep3 (Closing.zero Rc) c3 c4 w h)
    (hact : c4.active = c4.elems.length) (hst : c4.state = System4State.C) :
    ∃ L, c3 = ⟨0 :: L, 0, Rc, A⟩ := by
  obtain ⟨⟨ls, rs, le, rc, st, foc⟩, hrc, _, rfl, rfl⟩ := hrep
  simp only at hrc
  subst hrc
  cases foc with
  | setA xl b xr S => exfalso; simp [AC.to4] at hact
  | setB x0 x' S => exfalso; simp [AC.to4] at hact
  | setT x1 x' S => exfalso; simp [AC.to4] at hact
  | star => exfalso; simp [AC.to4] at hact
  | off =>
    simp only [AC.to4] at hst
    subst hst
    exact ⟨_, rfl⟩

/-! ## The block tape -/

/-- The System 4 tape of a block: the leading star, `r - 1` guards `{1, n}`
    with their stars, the guard `{0, 1, n - 1}`, and the program `orig`. -/
def blockTape (n r : Nat) (orig : List System4Elem) : List System4Elem :=
  System4Elem.star :: (preGuardPairs n (r - 1) ++ System4Elem.set (preM n) :: orig)

/-- The items of a block, right of its leading star. -/
def blockItems (w n r : Nat) (orig : List System4Elem) : List Item :=
  (preGuardPairs n (r - 1) ++ System4Elem.set (preM n) :: orig).map (toItem (2 ^ w))

/-- The abstract configuration at the entry of a block: the head on the
    leading star in state C, junk `L` to the left, the closing `0 :: Rc`. -/
def blockAC (w n r : Nat) (orig : List System4Elem) (L Rc : List (Fin 3)) : AC :=
  ⟨[], blockItems w n r orig, LeftEnd.junk L, Closing.zero Rc, System4State.C, Focus.star⟩

theorem blockAC_to4 (w n r : Nat) (orig : List System4Elem) (L Rc : List (Fin 3)) :
    (blockAC w n r orig L Rc).to4 = ⟨blockTape n r orig, 0, System4State.C⟩ := by
  simp [blockAC, AC.to4, blockItems, blockTape, List.map_map, Function.comp_def]

theorem blockAC_toL (w n r : Nat) (orig : List System4Elem) (L Rc : List (Fin 3)) :
    (blockAC w n r orig L Rc).toL
      = ⟨0 :: L, 0, renderR true (blockItems w n r orig) ++ 0 :: Rc, A⟩ := by
  simp [blockAC, AC.toL, LeftEnd.render, Closing.render]

theorem noAdjacentStars_preGuardPairs (n k : Nat) (T : List System4Elem)
    (hT : noAdjacentStars T = true) (hhead : ∀ e, T.head? = some e → e.isStar = false) :
    noAdjacentStars (preGuardPairs n k ++ T) = true := by
  induction k with
  | zero => simpa [preGuardPairs] using hT
  | succ k ih =>
    simp only [preGuardPairs, List.cons_append]
    refine noAdjacentStars_cons _ _ (fun c hc => by rw [List.head?_cons] at hc; rw [← Option.some.inj hc]; rfl) ?_
    refine noAdjacentStars_cons _ _ ?_ ih
    intro c hc
    cases k with
    | zero =>
      simp only [preGuardPairs, List.nil_append] at hc
      rw [hhead c hc]
      rfl
    | succ k =>
      simp only [preGuardPairs, List.cons_append, List.head?_cons] at hc
      rw [← Option.some.inj hc]; rfl

theorem preGuardPairs_getLast?_ne (n k : Nat) (T : List System4Elem) (hT : T ≠ [])
    (hlast : T.getLast? ≠ some System4Elem.star) :
    (preGuardPairs n k ++ T).getLast? ≠ some System4Elem.star := by
  rw [List.getLast?_append_of_ne_nil _ hT]
  exact hlast

theorem forall_mem_preGuardPairs (n k : Nat) (P : System4Elem → Prop)
    (h1 : P (System4Elem.set [1, (n : Int)])) (h2 : P System4Elem.star) :
    ∀ e ∈ preGuardPairs n k, P e := by
  induction k with
  | zero => simp [preGuardPairs]
  | succ k ih =>
    intro e he
    simp only [preGuardPairs, List.mem_cons] at he
    rcases he with rfl | rfl | he
    · exact h1
    · exact h2
    · exact ih e he

/-- The side conditions of a block at its entry: the width covers the fuel
    `h`, the guard parameter and the program's integers, the program tape is
    well-formed and ends with a set, and System 4 never turns at the left
    end of the block tape within the fuel. -/
theorem blockAC_OK (w n r h : Nat) (orig : List System4Elem) (L Rc : List (Fin 3))
    (hn : 3 ≤ n) (hN : h + 3 ≤ 2 ^ w) (hnw : n < 2 ^ w)
    (hwf : System4Config.WellFormed ⟨orig, 0, System4State.A⟩) (horig_ne : orig ≠ [])
    (hlast : orig.getLast? ≠ some System4Elem.star)
    (hb : ∀ S, System4Elem.set S ∈ orig → ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w)
    (hsafe : SafeC h ⟨blockTape n r orig, 0, System4State.C⟩) :
    (blockAC w n r orig L Rc).OK w h := by
  obtain ⟨hhead, hadj, hnd⟩ := hwf
  have hnd' : ∀ S, System4Elem.set S ∈ orig → S.Nodup := by
    intro S hS
    have := (List.all_eq_true.mp hnd) _ hS
    simpa [System4Elem.setNodup] using this
  obtain ⟨o0, orest, rfl⟩ := List.exists_cons_of_ne_nil horig_ne
  have ho0 : o0.isStar = false := by simpa [headNotStar] using hhead
  have hItem : ∀ e ∈ preGuardPairs n (r - 1) ++ System4Elem.set (preM n) :: o0 :: orest,
      ItemOK (2 ^ w) (h + 1) (toItem (2 ^ w) e) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · refine forall_mem_preGuardPairs n (r - 1) (fun e => ItemOK (2 ^ w) (h + 1) (toItem (2 ^ w) e)) ?_ trivial e he
      refine ItemOK_encSet w (h + 1) _ (by simp; omega) ?_ (by omega)
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> constructor <;> omega
    · rcases List.mem_cons.mp he with rfl | he
      · refine ItemOK_encSet w (h + 1) _ (by simp [preM]; omega) ?_ (by omega)
        intro x hx
        simp only [preM, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> constructor <;> omega
      · cases e with
        | star => trivial
        | set S => exact ItemOK_encSet w (h + 1) S (hnd' S he) (hb S he) (by omega)
  refine ⟨hN, ?_, by simp [blockAC], ?_, trivial, ?_, ?_⟩
  · rw [blockAC_to4]; exact hsafe
  · intro it hit
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hit
    exact hItem e he
  · show RightOK (blockItems w n r (o0 :: orest))
    unfold blockItems
    apply RightOK_map w
    · apply noAdjacentStars_preGuardPairs
      · exact noAdjacentStars_cons _ _ (fun c hc => by rw [List.head?_cons] at hc; rw [← Option.some.inj hc, ho0]; rfl) hadj
      · intro e he
        rw [List.head?_cons] at he
        rw [← Option.some.inj he]; rfl
    · exact preGuardPairs_getLast?_ne n (r - 1) _ (by simp) hlast
  · show LeftLast true [] ∧ HeadFirstTrue (blockItems w n r (o0 :: orest))
    refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
    unfold blockItems
    cases hr : r - 1 with
    | zero => simp only [preGuardPairs, List.nil_append, List.map_cons]; exact firstTrue_encSet w _
    | succ k => simp only [preGuardPairs, List.cons_append, List.map_cons]; exact firstTrue_encSet w _

/-! ## The run of a block on the System 4 side -/

theorem padCfg_entry (n r : Nat) (hr : 1 ≤ r) (orig : List System4Elem) :
    padCfg n r 0 [System4Elem.star] [] ⟨orig, 0, System4State.B⟩
      = ⟨System4Elem.star :: (guardPairs n (r - 1) ++ System4Elem.set (gset n 2) :: orig), 2 * r,
         System4State.B⟩ := by
  simp only [padCfg, Nat.sub_zero, merged_zero, sets_cons, sets_nil, List.cons_append,
    List.append_nil, List.nil_append, List.append_assoc, List.length_singleton,
    System4Config.mk.injEq, true_and, and_true]
  omega

/-- The truncated run of a block: the entry through the guards, then the
    padded tracking of the program's run after its first turn; the head is
    on the leading star only at time 0, in state C. -/
theorem block_run (n r : Nat) (hn : 3 ≤ n) (S0 : List Int) (rest : List System4Elem) (T4 : Nat)
    (cE : System4Config) (hT4 : 1 ≤ T4) (hr : T4 ≤ r) (hnT : T4 + 1 ≤ n)
    (hrun : System4.nSteps ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩ T4 = some cE)
    (hact : cE.active = cE.elems.length) :
    ∃ (H : Nat) (padT turns : Nat → Nat),
      System4.nSteps ⟨blockTape n r (System4Elem.set S0 :: rest), 0, System4State.C⟩ H
        = some (padCfg n r (turns (T4 - 1)) [System4Elem.star] [] cE) ∧
      (∀ h', SafeC h' ⟨blockTape n r (System4Elem.set S0 :: rest), 0, System4State.C⟩) ∧
      (∀ i, i < T4 - 1 → padT i < padT (i + 1)) ∧
      (∀ i, i + 1 ≤ T4 → 2 * r + padT i ≤ H ∧ ∃ ci,
        System4.nSteps ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩ (i + 1) = some ci ∧
        System4.nSteps ⟨blockTape n r (System4Elem.set S0 :: rest), 0, System4State.C⟩ (2 * r + padT i)
          = some (padCfg n r (turns i) [System4Elem.star] [] ci)) := by
  obtain ⟨N', hN'⟩ : ∃ N', T4 = N' + 1 := ⟨T4 - 1, by omega⟩
  subst hN'
  have hrunB : System4.nSteps ⟨System4Elem.set S0 :: rest, 0, System4State.B⟩ N' = some cE := by
    rw [Nat.add_comm, System4.nSteps_add, System4.nSteps_one, step_setA_zero, Option.bind_some] at hrun
    exact hrun
  obtain ⟨hentry, hentry_pos⟩ := entryRun n hn (r - 1) [] (System4Elem.set S0 :: rest)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hentry hentry_pos
  have hr1 : 1 ≤ r := by omega
  have h2r : 2 * (r - 1) + 2 = 2 * r := by omega
  rw [h2r, ← padCfg_entry n r hr1] at hentry
  obtain ⟨padT, turns, hp0, ht0, hmono, htr, hpos⟩ :=
    pad_schedule n r [System4Elem.star] [] N' ⟨System4Elem.set S0 :: rest, 0, System4State.B⟩
      (by omega) (by omega) cE hrunB
  have hblock : ∀ d, System4.nSteps ⟨blockTape n r (System4Elem.set S0 :: rest), 0, System4State.C⟩ (2 * r + d)
      = System4.nSteps (padCfg n r 0 [System4Elem.star] [] ⟨System4Elem.set S0 :: rest, 0, System4State.B⟩) d := by
    intro d
    rw [System4.nSteps_add]
    unfold blockTape
    rw [hentry, Option.bind_some]
  obtain ⟨-, cN, hcN, hpadN⟩ := htr N' (le_refl _)
  rw [hrunB] at hcN
  obtain rfl := Option.some.inj hcN
  refine ⟨2 * r + padT N', padT, turns, ?_, ?_, hmono, ?_⟩
  · rw [hblock, hpadN]
    simp
  · intro h' j _ c' hc'
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [System4.nSteps_zero] at hc'
      obtain rfl := Option.some.inj hc'
      exact Or.inr rfl
    · left
      rcases Nat.lt_or_ge j (2 * r + 1) with hlt | hge
      · unfold blockTape at hc'
        have := hentry_pos j hj (by omega) c' hc'
        omega
      · obtain ⟨d, rfl⟩ : ∃ d, j = 2 * r + d := ⟨j - 2 * r, by omega⟩
        rw [hblock] at hc'
        by_cases hd : d ≤ padT N'
        · have := hpos d hd c' hc'
          simp at this
          omega
        · exfalso
          have hstuck : System4.step (padCfg n r (turns N') [System4Elem.star] [] cE) = none := by
            have : padCfg n r (turns N') [System4Elem.star] [] cE
                = ⟨(padCfg n r (turns N') [System4Elem.star] [] cE).elems,
                   (padCfg n r (turns N') [System4Elem.star] [] cE).elems.length,
                   (padCfg n r (turns N') [System4Elem.star] [] cE).state⟩ := by
              simp only [padCfg, System4Config.mk.injEq, List.length_append, List.length_singleton,
                length_guardPairs, sets, List.length_map, length_merged, List.length_nil, true_and,
                and_true]
              omega
            rw [this, step_off]
          obtain ⟨e, he⟩ : ∃ e, d = padT N' + (e + 1) := ⟨d - padT N' - 1, by omega⟩
          rw [he, System4.nSteps_add, hpadN, Option.bind_some, System4.nSteps_succ, hstuck] at hc'
          cases hc'
  · intro i hi
    obtain ⟨hti, ci, hci, hpadi⟩ := htr i (by omega)
    refine ⟨by
      have := strictMono_of_succ padT N' hmono
      rcases Nat.lt_or_eq_of_le (show i ≤ N' by omega) with hlt | rfl
      · have := this i N' hlt (le_refl _); omega
      · omega, ci, ?_, ?_⟩
    · rw [Nat.add_comm, System4.nSteps_add, System4.nSteps_one, step_setA_zero, Option.bind_some]
      exact hci
    · rw [hblock, hpadi]

/-! ## A block -/

/-- The data of a block: the guard parameter `n`, the number of guards `r`,
    the width exponent `w`, the band `b`, the program tape `set S0 :: rest`,
    the length `H` of the truncated System 4 run, and the decoding times
    `dt` on that run. -/
structure BlockData where
  n : Nat
  r : Nat
  w : Nat
  b : Nat
  S0 : List Int
  rest : List System4Elem
  H : Nat
  dt : Nat → Nat

/-- The program tape of a block. -/
def BlockData.orig (bd : BlockData) : List System4Elem := System4Elem.set bd.S0 :: bd.rest

/-- The System 4 tape of a block. -/
def BlockData.tape (bd : BlockData) : List System4Elem := blockTape bd.n bd.r bd.orig

/-- The fuel of a block's `Rep3`: the run and the band. -/
def BlockData.fuel (bd : BlockData) : Nat := bd.H + bd.b

/-- The block `bd` emulates the first `k` steps of `tm` from `c`. -/
structure BlockSpec (tm : Machine) (c : BiTM.Config) (k : Nat) (bd : BlockData) : Prop where
  hn : 3 ≤ bd.n
  hN : bd.fuel + 3 ≤ 2 ^ bd.w
  hnw : bd.n < 2 ^ bd.w
  hwf : System4Config.WellFormed ⟨bd.orig, 0, System4State.A⟩
  hlast : bd.orig.getLast? ≠ some System4Elem.star
  hb : ∀ S, System4Elem.set S ∈ bd.orig → ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ bd.w
  hsafe : SafeC bd.fuel ⟨bd.tape, 0, System4State.C⟩
  hexit : ∃ cE, System4.nSteps ⟨bd.tape, 0, System4State.C⟩ bd.H = some cE ∧
    cE.state = System4State.C ∧ cE.active = cE.elems.length
  hmono : ∀ i, i < k → bd.dt i < bd.dt (i + 1)
  hdec : ∀ i, i ≤ k → bd.dt i ≤ bd.H ∧ ∃ ci Lp K R, BiTM.nSteps tm c i = some ci ∧ K ≠ [] ∧
    System4.nSteps ⟨bd.tape, 0, System4State.C⟩ (bd.dt i)
      = some ⟨Lp ++ sets K ++ System4Elem.star :: R, Lp.length, System4State.B⟩ ∧
    (decodeS4 ⟨sets K ++ System4Elem.star :: R, 0, System4State.B⟩ bd.b).bind decodeBag
      = some (dbl (ctsOfCfg tm.numStates ci).data)

/-- The run of a block is not empty: at time 0 the head is on the leading
    star, not past the end. -/
theorem BlockSpec.H_pos {tm : Machine} {c : BiTM.Config} {k : Nat} {bd : BlockData}
    (hspec : BlockSpec tm c k bd) : 1 ≤ bd.H := by
  obtain ⟨cE, hcE, -, hact⟩ := hspec.hexit
  by_contra h
  have h0 : bd.H = 0 := by omega
  rw [h0, System4.nSteps_zero] at hcE
  obtain rfl := Option.some.inj hcE
  simp [BlockData.tape, blockTape] at hact

/-- A block for every `k`: the emulation of the first `k` steps of a
    well-formed binary machine that runs at least `k` steps. -/
theorem block_exists (tm : Machine) (hwf : WF tm) (c : BiTM.Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) (k : Nat) (ck : BiTM.Config)
    (hrun : BiTM.nSteps tm c k = some ck) : ∃ bd : BlockData, BlockSpec tm c k bd := by
  -- the tag schedule of the run and the cyclic tag run of `tt k` cycles
  obtain ⟨tt, ht0, htmono, httr⟩ := ForwardSim_nSteps (tm_tag_forwardSim tm hwf) k c
    ((word c).map (enc tm.numStates)) ⟨hv, hst, rfl⟩ ck (by rw [tmSys_nSteps]; exact hrun)
  have httle : ∀ j, j ≤ k → tt j ≤ tt k := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact le_of_lt (strictMono_of_succ tt k htmono j k hlt (le_refl _))
    · exact le_refl _
  have hlen := tagToCTS_appendants_length (tagK tm tm.numStates) (K_pos tm.numStates)
  obtain ⟨cn, wn, hcn, hwn, -, -, rfl⟩ := httr k (le_refl k)
  rw [tagSysK_nSteps] at hwn
  have hcts_n := cts_of_tag (tagK tm tm.numStates) (K_pos _) (tt k) _ _ hwn
  have hne : (tagConfigToCTS (1 + 84 * tm.numStates) ((word cn).map (enc tm.numStates))).data ≠ [] := by
    show tagWordEncode _ _ ≠ []
    intro h
    have h1 := tagWordEncode_length (1 + 84 * tm.numStates) ((word cn).map (enc tm.numStates))
    rw [h, List.length_nil, List.length_map] at h1
    have h2 := length_word cn
    have h3 : 0 < (1 + 84 * tm.numStates) * (word cn).length := Nat.mul_pos (by omega) (by omega)
    omega
  -- the System 4 emulation of that cyclic tag run
  obtain ⟨s0, f, b, T4, cE, t4, hs0, hf1, hbag1, hrules1, hrunT4, hstE, hactE, h4mono, h4tr⟩ :=
    system4_emulation (tagToCTS (tagK tm tm.numStates) (K_pos _)) (ctsOfCfg tm.numStates c) (tt k) _
      (by rw [hlen]; exact hcts_n) hne
  have hpos : 0 < 2 * (1 + 84 * tm.numStates) := by omega
  have hT4 : 1 ≤ T4 := by
    have := (h4tr 0 (Nat.zero_le _)).1
    omega
  -- the block around it
  obtain ⟨S0, rest, horig⟩ : ∃ S0 rest, (system5ToSystem4 s0 f).elems = System4Elem.set S0 :: rest :=
    ⟨encodeBag s0.bag, _, rfl⟩
  have hc40 : system5ToSystem4 s0 f = ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩ := by
    rw [← horig]; rfl
  rw [hc40] at hrunT4 h4tr
  obtain ⟨n, hn⟩ : ∃ n, n = T4 + 3 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = T4 + 1 := ⟨_, rfl⟩
  obtain ⟨H, padT, turns, hH, hsafe, hpmono, hptr⟩ :=
    block_run n r (by omega) S0 rest T4 cE hT4 (by omega) (by omega) hrunT4 hactE
  obtain ⟨w, hw⟩ : ∃ w, w = H + b + n + 3 * f + 6 := ⟨_, rfl⟩
  have hw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hwf4 := system5ToSystem4_wellFormed s0 f hf1
  have hlast4 := system5ToSystem4_last_set s0 f hf1
  rw [hc40] at hwf4 hlast4
  refine ⟨⟨n, r, w, b, S0, rest, H, fun i => 2 * r + padT (t4 (2 * (1 + 84 * tm.numStates) * tt i))⟩,
    ?_, ?_, ?_, hwf4, hlast4, ?_, hsafe _, ⟨_, hH, ?_, ?_⟩, ?_, ?_⟩
  · show 3 ≤ n; omega
  · show H + b + 3 ≤ 2 ^ w; omega
  · show n < 2 ^ w; omega
  · intro S hS e he
    have := system5ToSystem4_elem_lt s0 f hbag1 hrules1 S (by rw [hc40]; exact hS) e he
    show 0 ≤ e ∧ e.toNat < 2 ^ w
    constructor <;> omega
  · simp only [padCfg]; exact hstE
  · simp only [padCfg, List.length_append, List.length_singleton, length_guardPairs, sets,
      List.length_map, length_merged, List.length_nil, hactE]
    omega
  · intro i hi
    show 2 * r + padT (t4 (2 * (1 + 84 * tm.numStates) * tt i))
      < 2 * r + padT (t4 (2 * (1 + 84 * tm.numStates) * tt (i + 1)))
    have h1 := htmono i hi
    have h2 := httle (i + 1) hi
    have h3 : 2 * (1 + 84 * tm.numStates) * tt (i + 1) ≤ 2 * (1 + 84 * tm.numStates) * tt k :=
      Nat.mul_le_mul_left _ h2
    have h4 : t4 (2 * (1 + 84 * tm.numStates) * tt i) < t4 (2 * (1 + 84 * tm.numStates) * tt (i + 1)) :=
      strictMono_of_succ t4 _ h4mono _ _ (Nat.mul_lt_mul_of_pos_left h1 hpos) (by rw [hlen]; exact h3)
    have h5 := (h4tr (2 * (1 + 84 * tm.numStates) * tt (i + 1)) (by rw [hlen]; exact h3)).1
    have := strictMono_of_succ padT (T4 - 1) hpmono _ _ h4 (by omega)
    omega
  · intro i hi
    have hle : 2 * (1 + 84 * tm.numStates) * tt i
        ≤ (tagToCTS (tagK tm tm.numStates) (K_pos _)).appendants.length * tt k := by
      rw [hlen]; exact Nat.mul_le_mul_left _ (httle i hi)
    obtain ⟨hT, ci', K, R, hci', hKne, hc4i, hdec⟩ := h4tr _ hle
    obtain ⟨ci, wi, hci, hwi, hvi, hsti, rfl⟩ := httr i hi
    rw [tagSysK_nSteps] at hwi
    have hcts_i := cts_of_tag (tagK tm tm.numStates) (K_pos _) (tt i) _ _ hwi
    rw [show ctsOfCfg tm.numStates c
        = tagConfigToCTS (1 + 84 * tm.numStates) ((word c).map (enc tm.numStates)) from rfl,
      hcts_i] at hci'
    obtain rfl := Option.some.inj hci'
    obtain ⟨hpt, ci4, hci4, hpad⟩ := hptr (t4 (2 * (1 + 84 * tm.numStates) * tt i)) hT
    rw [hc4i] at hci4
    obtain rfl := Option.some.inj hci4
    refine ⟨hpt, ci,
      [System4Elem.star] ++ guardPairs n (r - 1 - turns (t4 (2 * (1 + 84 * tm.numStates) * tt i)))
        ++ sets (merged n (turns (t4 (2 * (1 + 84 * tm.numStates) * tt i)))),
      K, R, by rw [← tmSys_nSteps]; exact hci, hKne, ?_, hdec⟩
    show System4.nSteps ⟨blockTape n r (System4Elem.set S0 :: rest), 0, System4State.C⟩ _ = _
    rw [hpad]
    simp only [padCfg, List.append_assoc, List.append_nil, List.length_append,
      List.length_singleton, length_guardPairs, sets, List.length_map, length_merged,
      Nat.add_zero, Nat.add_assoc]

/-! ## The run of a block on the System 3 side -/

/-- The System 3 cells of a block: its items rendered, then its closing 0. -/
def BlockData.cells (bd : BlockData) : List (Fin 3) :=
  renderR true (blockItems bd.w bd.n bd.r bd.orig) ++ [0]

/-- The System 3 configuration at the entry of a block: the head on the 0
    left of the block in state A, a 0 to its left, the block and the rest
    `Rc` of the tape to its right. -/
def entry3 (L : List (Fin 3)) (bd : BlockData) (Rc : List (Fin 3)) : LConfig :=
  ⟨0 :: L, 0, bd.cells ++ Rc, A⟩

theorem entry3_eq (L : List (Fin 3)) (bd : BlockData) (Rc : List (Fin 3)) :
    entry3 L bd Rc = (blockAC bd.w bd.n bd.r bd.orig L Rc).toL := by
  rw [blockAC_toL]
  simp [entry3, BlockData.cells]

theorem rep3_entry (tm : Machine) (c : BiTM.Config) (k : Nat) (bd : BlockData)
    (hspec : BlockSpec tm c k bd) (L Rc : List (Fin 3)) :
    Rep3 (Closing.zero Rc) (entry3 L bd Rc) ⟨bd.tape, 0, System4State.C⟩ bd.w bd.fuel :=
  ⟨blockAC bd.w bd.n bd.r bd.orig L Rc, rfl,
    blockAC_OK bd.w bd.n bd.r bd.fuel bd.orig L Rc hspec.hn hspec.hN hspec.hnw hspec.hwf
      (List.cons_ne_nil _ _) hspec.hlast hspec.hb hspec.hsafe,
    entry3_eq L bd Rc, (blockAC_to4 _ _ _ _ _ _).symm⟩

/-- The System 3 run of a block from its entry: it reaches the entry of the
    next block (the head on the closing 0 in state A) and on the way, at
    strictly increasing times, tapes that decode to the first `k`
    configurations of the machine. -/
theorem block_sys3 (tm : Machine) (c : BiTM.Config) (k : Nat) (bd : BlockData)
    (hspec : BlockSpec tm c k bd) (L Rc : List (Fin 3)) :
    ∃ (T3 : Nat) (L' : List (Fin 3)) (t3 : Nat → Nat),
      1 ≤ T3 ∧ lnSteps sys3 (entry3 L bd Rc) T3 = some ⟨0 :: L', 0, Rc, A⟩ ∧
      (∀ i, i < k → t3 i < t3 (i + 1)) ∧
      (∀ i, i ≤ k → t3 i ≤ T3 ∧ ∃ ci c3, BiTM.nSteps tm c i = some ci ∧
        lnSteps sys3 (entry3 L bd Rc) (t3 i) = some c3 ∧
        decodeW23 (2 ^ bd.w) bd.b (toBi (phi2 (phi3 c3)))
          = some (dbl (ctsOfCfg tm.numStates ci).data) ∧
        0 ∈ (toBi (phi2 (phi3 c3))).right ∧ (toBi (phi2 (phi3 c3))).state = 2) := by
  obtain ⟨cE, hcE, hstE, hactE⟩ := hspec.hexit
  have hHf : bd.H ≤ bd.fuel := Nat.le_add_right _ _
  obtain ⟨times, hsched⟩ := ForwardSim_nSteps (sys4_sys3_forwardSim bd.w (Closing.zero Rc))
    bd.H (⟨bd.tape, 0, System4State.C⟩, bd.fuel) (entry3 L bd Rc) (rep3_entry tm c k bd hspec L Rc)
    (cE, bd.fuel - bd.H) (by rw [fueled_nSteps _ _ _ _ hHf, system4Sys_nSteps, hcE]; rfl)
  have hHle : bd.H ≤ times bd.H := IsSimSchedule_le hsched bd.H (le_refl _)
  obtain ⟨-, hmono, htr⟩ := hsched
  have hat : ∀ j, j ≤ bd.H → ∃ c4 c3, System4.nSteps ⟨bd.tape, 0, System4State.C⟩ j = some c4 ∧
      lnSteps sys3 (entry3 L bd Rc) (times j) = some c3 ∧
      Rep3 (Closing.zero Rc) c3 c4 bd.w (bd.fuel - j) := by
    intro j hj
    obtain ⟨⟨c4, g⟩, c3, hs, ht, hrep⟩ := htr j hj
    rw [fueled_nSteps _ _ _ _ (by omega), system4Sys_nSteps] at hs
    cases h4 : System4.nSteps ⟨bd.tape, 0, System4State.C⟩ j with
    | none => rw [h4] at hs; simp at hs
    | some c4' =>
      rw [h4, Option.map_some] at hs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
      exact ⟨c4', c3, rfl, ht, hrep⟩
  have htle : ∀ j, j ≤ bd.H → times j ≤ times bd.H := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact le_of_lt (strictMono_of_succ times bd.H hmono j bd.H hlt (le_refl _))
    · exact le_refl _
  obtain ⟨c4H, c3H, h4H, h3H, hrepH⟩ := hat bd.H (le_refl _)
  rw [hcE] at h4H
  obtain rfl := Option.some.inj h4H
  obtain ⟨L', rfl⟩ := rep3_exit_zero Rc c3H _ bd.w _ hrepH hactE hstE
  refine ⟨times bd.H, L', fun i => times (bd.dt i), by have := hspec.H_pos; omega, h3H, ?_, ?_⟩
  · intro i hi
    exact strictMono_of_succ times bd.H hmono _ _ (hspec.hmono i hi) (hspec.hdec (i + 1) hi).1
  · intro i hi
    obtain ⟨hdt, ci, Lp, K, R, hci, hK, h4i, hdec⟩ := hspec.hdec i hi
    obtain ⟨c4i, c3i, h4i', h3i, hrepi⟩ := hat (bd.dt i) hdt
    rw [h4i] at h4i'
    obtain rfl := Option.some.inj h4i'
    obtain ⟨hd, hz, hstB⟩ := rep3_decode c3i Lp K R bd.w _ bd.b hK
      (by show bd.b ≤ bd.H + bd.b - bd.dt i + 1; omega) _ hrepi
    exact ⟨htle _ hdt, ci, c3i, hci, h3i, by rw [hd, hdec], hz, hstB⟩

/-! ## The chain of blocks -/

/-- The cells of the blocks `j, ..., j + n - 1`. -/
def segCells (bd : Nat → BlockData) (j n : Nat) : List (Fin 3) :=
  ((List.range' j n).map fun i => (bd i).cells).flatten

@[simp] theorem segCells_zero (bd : Nat → BlockData) (j : Nat) : segCells bd j 0 = [] := rfl

theorem segCells_succ (bd : Nat → BlockData) (j n : Nat) :
    segCells bd j (n + 1) = (bd j).cells ++ segCells bd (j + 1) n := by
  simp [segCells, List.range'_succ]

theorem segCells_add (bd : Nat → BlockData) (j a b : Nat) :
    segCells bd j (a + b) = segCells bd j a ++ segCells bd (j + a) b := by
  unfold segCells
  rw [← List.range'_append, Nat.one_mul, List.map_append, List.flatten_append]

theorem segCells_length_ge (bd : Nat → BlockData) (j n : Nat) : n ≤ (segCells bd j n).length := by
  induction n generalizing j with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [segCells_succ, List.length_append]
    have := ih (j + 1)
    simp only [BlockData.cells, List.length_append, List.length_singleton]
    omega

/-- The System 3 run through the blocks `j, ..., j + n - 1`, entry to entry;
    block `j` emulates `kk j` steps. -/
theorem chain_sys3 (tm : Machine) (c : BiTM.Config) (bd : Nat → BlockData) (kk : Nat → Nat)
    (hbd : ∀ j, BlockSpec tm c (kk j) (bd j)) (n : Nat) :
    ∀ (j : Nat) (L Rc : List (Fin 3)), ∃ (T : Nat) (L' : List (Fin 3)), n ≤ T ∧
      lnSteps sys3 ⟨0 :: L, 0, segCells bd j n ++ Rc, A⟩ T = some ⟨0 :: L', 0, Rc, A⟩ := by
  induction n with
  | zero => intro j L Rc; exact ⟨0, L, le_refl _, by simp⟩
  | succ n ih =>
    intro j L Rc
    obtain ⟨T1, L1, -, hT1, h1, -, -⟩ :=
      block_sys3 tm c (kk j) (bd j) (hbd j) L (segCells bd (j + 1) n ++ Rc)
    obtain ⟨T2, L2, hT2, h2⟩ := ih (j + 1) L1 Rc
    refine ⟨T1 + T2, L2, by omega, ?_⟩
    rw [lnSteps_add]
    have : (⟨0 :: L, 0, segCells bd j (n + 1) ++ Rc, A⟩ : LConfig)
        = entry3 L (bd j) (segCells bd (j + 1) n ++ Rc) := by
      simp [entry3, segCells_succ]
    rw [this, h1, Option.bind_some, h2]

/-- The System 3 start of the emulation of `k` steps: the head on a 2 in
    state B, the 0 that will be the left end of block 0 to its right, then
    the blocks `0, ..., k`. -/
def start3 (bd : Nat → BlockData) (k : Nat) : LConfig :=
  ⟨[], 2, 0 :: segCells bd 0 (k + 1), B⟩

theorem start3_step (bd : Nat → BlockData) (k : Nat) :
    lstep sys3 (start3 bd k) = some ⟨[0], 0, segCells bd 0 (k + 1), A⟩ := rfl

/-- The wolfram23 start of the emulation of `k` steps: `start3` relabeled. -/
def startFin (bd : Nat → BlockData) (k : Nat) : BiTM.Config :=
  ⟨2, [], 2, 0 :: (segCells bd 0 (k + 1)).map Fin.val⟩

theorem startFin_eq (bd : Nat → BlockData) (k : Nat) :
    startFin bd k = toBi (phi2 (phi3 (start3 bd k))) := rfl

/-- The emulation of the first `kk k` steps on the finite tape of the blocks
    `0, ..., k`: wolfram23 from `startFin bd k` decodes, at strictly
    increasing times, to the first `kk k` configurations of the machine, the
    run staying on the explicit tape. -/
theorem stage_w23 (tm : Machine) (c : BiTM.Config) (bd : Nat → BlockData) (kk : Nat → Nat)
    (hbd : ∀ j, BlockSpec tm c (kk j) (bd j)) (k : Nat) :
    ∃ (times : Nat → Nat) (T : Nat), k < times (kk k) ∧
      (∀ i, i < kk k → times i < times (i + 1)) ∧
      (∀ i, i ≤ kk k → times i ≤ T ∧ ∃ ci cfgi, BiTM.nSteps tm c i = some ci ∧
        BiTM.nSteps wolfram23 (startFin bd k) (times i) = some cfgi ∧
        decodeW23 (2 ^ (bd k).w) (bd k).b cfgi = some (dbl (ctsOfCfg tm.numStates ci).data) ∧
        0 ∈ cfgi.right ∧ cfgi.state = 2) ∧
      (∀ τ, τ ≤ T → ∃ cfgτ, BiTM.nSteps wolfram23 (startFin bd k) τ = some cfgτ ∧
        biSize cfgτ = biSize (startFin bd k)) := by
  obtain ⟨P0, L0, hkP0, hP0⟩ := chain_sys3 tm c bd kk hbd k 0 [] (bd k).cells
  obtain ⟨T3, L', t3, -, -, hmono3, htr3⟩ := block_sys3 tm c (kk k) (bd k) (hbd k) L0 []
  have hentry : lnSteps sys3 (start3 bd k) (P0 + 1) = some (entry3 L0 (bd k) []) := by
    rw [lnSteps_succ, start3_step, Option.bind_some]
    have hseg : segCells bd 0 (k + 1) = segCells bd 0 k ++ (bd k).cells := by
      rw [segCells_add, Nat.zero_add]
      simp [segCells_succ]
    simpa [entry3, hseg] using hP0
  obtain ⟨m, hm⟩ : ∃ m, m = kk k := ⟨_, rfl⟩
  rw [← hm] at hmono3 htr3 ⊢
  have h3le : ∀ i, i ≤ m → t3 i ≤ t3 m := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with hlt | rfl
    · exact le_of_lt (strictMono_of_succ t3 m hmono3 i m hlt (le_refl _))
    · exact le_refl _
  obtain ⟨-, cm, c3m, -, h3m, -, -, -⟩ := htr3 m (le_refl _)
  have hrun3 : lnSteps sys3 (start3 bd k) (P0 + 1 + t3 m) = some c3m := by
    rw [lnSteps_add, hentry, Option.bind_some, h3m]
  obtain ⟨times0, hsched0⟩ := ForwardSim_nSteps sys3_sys0_forwardSim (P0 + 1 + t3 m)
    (start3 bd k) (phi2 (phi3 (start3 bd k))) rfl c3m hrun3
  have hTle : P0 + 1 + t3 m ≤ times0 (P0 + 1 + t3 m) := IsSimSchedule_le hsched0 _ (le_refl _)
  obtain ⟨-, hmono0, htr0⟩ := hsched0
  have hst0 : (phi2 (phi3 (start3 bd k))).state ≠ C := phi2_state_ne_C _
  have h0le : ∀ j, j ≤ P0 + 1 + t3 m → times0 j ≤ times0 (P0 + 1 + t3 m) := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact le_of_lt (strictMono_of_succ times0 _ hmono0 j _ hlt (le_refl _))
    · exact le_refl _
  obtain ⟨c3m', c0m, -, h0m, rfl⟩ := htr0 _ (le_refl _)
  refine ⟨fun i => times0 (P0 + 1 + t3 i), times0 (P0 + 1 + t3 m), by dsimp only; omega, ?_, ?_, ?_⟩
  · intro i hi
    exact strictMono_of_succ times0 _ hmono0 _ _ (by have := hmono3 i hi; omega)
      (by have := h3le (i + 1) hi; omega)
  · intro i hi
    obtain ⟨-, ci, c3i, hci, h3i, hdec, hz, hstB⟩ := htr3 i hi
    have hji : P0 + 1 + t3 i ≤ P0 + 1 + t3 m := by have := h3le i hi; omega
    obtain ⟨c3i', -, h3i', h0i, rfl⟩ := htr0 _ hji
    have h3i'' : lnSteps sys3 (start3 bd k) (P0 + 1 + t3 i) = some c3i := by
      rw [lnSteps_add, hentry, Option.bind_some, h3i]
    obtain rfl := Option.some.inj (h3i''.symm.trans h3i')
    refine ⟨h0le _ hji, ci, toBi (phi2 (phi3 c3i)), hci, ?_, hdec, hz, hstB⟩
    rw [startFin_eq]
    exact (toBi_run _ hst0 _ _ h0i).1
  · intro τ hτ
    obtain ⟨cτ, hcτ⟩ := StepSys.nSteps_some_of_le (lsys sys0) _ _ _ τ hτ h0m
    refine ⟨toBi cτ, ?_, ?_⟩
    · rw [startFin_eq]; exact (toBi_run _ hst0 τ cτ hcτ).1
    · rw [startFin_eq, biSize_toBi, biSize_toBi, lnSteps_length sys0 _ τ cτ hcτ]

/-! ## The infinite tape -/

/-- The infinite tape right of the head: a 0, then the cells of all the
    blocks in order; the `i`-th of those is read off the first `i + 1`
    blocks, which have at least `i + 1` cells. -/
def tape (bd : Nat → BlockData) : Nat → Nat
  | 0 => 0
  | i + 1 => ((segCells bd 0 (i + 1))[i]?.getD 0).val

theorem tape_lt (bd : Nat → BlockData) (i : Nat) : tape bd i < 3 := by
  cases i with
  | zero => simp [tape]
  | succ i => exact Fin.isLt _

theorem segCells_getElem?_of_le (bd : Nat → BlockData) (m m' i : Nat) (hmm : m ≤ m')
    (hi : i < (segCells bd 0 m).length) : (segCells bd 0 m')[i]? = (segCells bd 0 m)[i]? := by
  obtain ⟨e, rfl⟩ : ∃ e, m' = m + e := ⟨m' - m, by omega⟩
  rw [segCells_add, List.getElem?_append_left hi]

theorem tape_succ (bd : Nat → BlockData) (m i : Nat) (hi : i < (segCells bd 0 m).length) :
    ((segCells bd 0 m).map Fin.val)[i]? = some (tape bd (i + 1)) := by
  have hi' : i < (segCells bd 0 (i + 1)).length :=
    lt_of_lt_of_le (Nat.lt_succ_self i) (segCells_length_ge bd 0 (i + 1))
  have heq : (segCells bd 0 m)[i]? = (segCells bd 0 (i + 1))[i]? := by
    rcases Nat.le_total m (i + 1) with h | h
    · exact (segCells_getElem?_of_le bd m (i + 1) i h hi).symm
    · exact segCells_getElem?_of_le bd (i + 1) m i h hi'
  rw [List.getElem?_map, heq, List.getElem?_eq_getElem hi']
  simp [tape, List.getElem?_eq_getElem hi']

/-- wolfram23 at the left end of an infinite tape: state B on a 2. -/
def istart (t : Nat → Nat) : IConfig := ⟨2, [], 2, t⟩

theorem startFin_agree (bd : Nat → BlockData) (k : Nat) : Agree (startFin bd k) (istart (tape bd)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    simp only [startFin, List.length_cons, List.length_map] at hi
    simp only [startFin, List.getElem?_cons_succ]
    exact tape_succ bd (k + 1) i (by omega)

/-- A valid infinite configuration of wolfram23: state A or B, every cell
    0, 1 or 2. -/
def IValid (d : IConfig) : Prop :=
  (d.state = 1 ∨ d.state = 2) ∧ d.head < 3 ∧ (∀ x ∈ d.left, x < 3) ∧ ∀ i, d.right i < 3

theorem wolfram23_rule (s a : Nat) (hs : s = 1 ∨ s = 2) (ha : a < 3) :
    ((wolfram23.transition s a).nextState = 1 ∨ (wolfram23.transition s a).nextState = 2) ∧
      (wolfram23.transition s a).write < 3 := by
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases hs with rfl | rfl <;> rcases ha' with rfl | rfl | rfl <;> decide

/-- wolfram23 never halts on a valid infinite configuration. -/
theorem istep_valid (d : IConfig) (h : IValid d) :
    ∃ d', istep wolfram23 d = some d' ∧ IValid d' := by
  obtain ⟨hs, hh, hl, hr⟩ := h
  obtain ⟨s, L, a, R⟩ := d
  simp only at hs hh hl hr
  obtain ⟨hnext, hwrite⟩ := wolfram23_rule s a hs hh
  have hs0 : s ≠ 0 := by omega
  unfold istep
  simp only [beq_iff_eq, hs0, if_false]
  cases hd : (wolfram23.transition s a).dir with
  | L =>
    refine ⟨_, rfl, hnext, ?_, ?_, ?_⟩
    · cases L with
      | nil => simp [readHead]
      | cons x L' => simp only [readHead]; exact hl x (List.mem_cons_self ..)
    · intro x hx
      cases L with
      | nil => simp [readHead] at hx
      | cons y L' => simp only [readHead] at hx; exact hl x (List.mem_cons_of_mem _ hx)
    · intro i
      by_cases hi : i = 0
      · simp [hi, hwrite]
      · simp only [hi, if_false]; exact hr _
  | R =>
    refine ⟨_, rfl, hnext, hr 0, ?_, fun i => hr _⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hwrite
    · exact hl x hx

theorem inSteps_valid (d : IConfig) (h : IValid d) (τ : Nat) :
    ∃ dτ, inSteps wolfram23 d τ = some dτ ∧ IValid dτ := by
  induction τ generalizing d with
  | zero => exact ⟨d, rfl, h⟩
  | succ τ ih =>
    obtain ⟨d1, hd1, hv1⟩ := istep_valid d h
    obtain ⟨dτ, hdτ, hvτ⟩ := ih d1 hv1
    exact ⟨dτ, by rw [inSteps_succ, hd1, Option.bind_some]; exact hdτ, hvτ⟩

theorem istart_valid (t : Nat → Nat) (ht : ∀ i, t i < 3) : IValid (istart t) :=
  ⟨Or.inr rfl, by show (2 : Nat) < 3; decide, fun x hx => by simp [istart] at hx, ht⟩

/-- A run of a well-formed machine keeps its configurations valid and their
    states below `numStates`. -/
theorem nSteps_valid (tm : Machine) (hwf : WF tm) (c : Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) : ∀ (n : Nat) (cn : Config), BiTM.nSteps tm c n = some cn →
    ValidCfg cn ∧ cn.state < tm.numStates := by
  intro n
  induction n generalizing c with
  | zero =>
    intro cn h
    simp only [BiTM.nSteps, Option.some.injEq] at h
    subst h
    exact ⟨hv, hst⟩
  | succ n ih =>
    intro cn h
    rw [biNSteps_succ'] at h
    cases hs : BiTM.step tm c with
    | none => rw [hs] at h; cases h
    | some c1 =>
      rw [hs, Option.bind_some] at h
      obtain ⟨hv1, hst1⟩ := step_valid tm hwf c c1 hv hst hs
      exact ih c1 hv1 hst1 cn h

/-! ## T6: the infinite form of Conjecture 0 -/

/-- The emulation of the first `k` steps on the infinite tape of a sequence
    of blocks, block `j` emulating `m j` steps with `m j` the last step below
    `j` at which the run of `tm` is defined: the schedule, the head never
    leaving the tape to the left before the end of the schedule, the decodes. -/
theorem stage_infinite (tm : Machine) (hwf : WF tm) (c : Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) (m : Nat → Nat) (bd : Nat → BlockData)
    (hm : ∀ j, m j ≤ j ∧ (∀ i, i ≤ j → (BiTM.nSteps tm c i).isSome → i ≤ m j) ∧
      BlockSpec tm c (m j) (bd j)) (k : Nat) :
    ∃ (w b W : Nat) (times : Nat → Nat), k < times k ∧
      (∀ i, i < k → (BiTM.nSteps tm c (i + 1)).isSome → times i < times (i + 1)) ∧
      (∀ τ, τ < times k → ∀ d, inSteps wolfram23 (istart (tape bd)) τ = some d → d.left = [] →
        (wolfram23.transition d.state d.head).dir = Dir.R) ∧
      (∀ i ci, i ≤ k → BiTM.nSteps tm c i = some ci → ∃ d,
        inSteps wolfram23 (istart (tape bd)) (times i) = some d ∧ d.state = 2 ∧
        ∀ W', W ≤ W' → decodeTM tm.numStates (2 ^ w) b (truncI W' d) = some (canon ci)) := by
  obtain ⟨hmk, hmax, -⟩ := hm k
  obtain ⟨times, T, hkT, hmono, htr, hsz⟩ := stage_w23 tm c bd m (fun j => (hm j).2.2) k
  have hagree := startFin_agree bd k
  have hszτ : ∀ τ, τ ≤ T → ∀ cτ, BiTM.nSteps wolfram23 (startFin bd k) τ = some cτ →
      biSize cτ = biSize (startFin bd k) := by
    intro τ hτ cτ hcτ
    obtain ⟨cτ', h', hsz'⟩ := hsz τ hτ
    rw [hcτ] at h'
    obtain rfl := Option.some.inj h'
    exact hsz'
  refine ⟨(bd k).w, (bd k).b, biSize (startFin bd k), fun i => times (min i (m k)),
    by dsimp only; rw [Nat.min_eq_right hmk]; exact hkT, ?_, ?_, ?_⟩
  · intro i hi hdef
    have h1 : i + 1 ≤ m k := hmax (i + 1) hi hdef
    dsimp only
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left h1]
    exact hmono i (by omega)
  · intro τ hτ d hd hL
    dsimp only at hτ
    rw [Nat.min_eq_right hmk] at hτ
    have hTk := (htr (m k) (le_refl _)).1
    obtain ⟨cτ, hcτ, hszτ'⟩ := hsz τ (by omega)
    obtain ⟨cτ1, hcτ1, hszτ1⟩ := hsz (τ + 1) (by omega)
    obtain ⟨dτ, hdτ, hag⟩ := agree_run wolfram23 τ _ _ hagree (fun τ' hτ' => hszτ τ' (by omega)) cτ hcτ
    rw [hd] at hdτ
    obtain rfl := Option.some.inj hdτ
    obtain ⟨hs, hl, hh, -⟩ := hag
    rw [biNSteps_add, hcτ, Option.bind_some, biNSteps_one] at hcτ1
    by_contra hdir
    have hdirL : (wolfram23.transition cτ.state cτ.head).dir = Dir.L := by
      rw [hs, hh]
      cases h : (wolfram23.transition d.state d.head).dir with
      | L => rfl
      | R => exact absurd h hdir
    have hq : cτ.state ≠ 0 := by
      intro h0
      obtain ⟨q, Lc, a, Rc⟩ := cτ
      simp only at h0
      subst h0
      simp [BiTM.step] at hcτ1
    obtain ⟨q, Lc, a, Rc⟩ := cτ
    simp only at hs hl hh hdirL hq hszτ'
    rw [step_L wolfram23 q Lc a Rc hq hdirL] at hcτ1
    obtain rfl := Option.some.inj hcτ1
    rw [hl, hL] at hszτ'
    simp only [biSize, readHead, hl, hL, List.length_nil, List.length_cons] at hszτ1 hszτ'
    omega
  · intro i ci hi hci
    have him : i ≤ m k := hmax i hi (by rw [hci]; rfl)
    dsimp only
    rw [Nat.min_eq_left him]
    obtain ⟨hTi, ci', cfgi, hci', hcfgi, hdec, hz, hstB⟩ := htr i him
    rw [hci] at hci'
    obtain rfl := Option.some.inj hci'
    obtain ⟨d, hd, hag⟩ := agree_run wolfram23 (times i) _ _ hagree
      (fun τ hτ => hszτ τ (by omega)) cfgi hcfgi
    refine ⟨d, hd, by rw [← hag.1]; exact hstB, ?_⟩
    intro W' hW'
    have hW : cfgi.right.length ≤ W' := by
      have := hszτ _ hTi cfgi hcfgi
      unfold biSize at this hW'
      omega
    rw [decodeTM_trunc _ _ _ _ cfgi d hag hW hz]
    unfold decodeTM
    rw [hdec, Option.bind_some, undbl_dbl, Option.bind_some]
    obtain ⟨hvi, hsti⟩ := nSteps_valid tm hwf c hv hst i ci hci
    exact decodeCTS_word tm.numStates ci hvi hsti

/-- T6 (PLAN.md section 2), Smith's Conjecture 0 in infinite form. For a
    well-formed binary machine `tm` and a valid configuration `c` there is one
    right-infinite tape of cells 0, 1, 2 on which wolfram23, started at the
    left end in state B on a 2, runs forever without ever moving left from
    the first cell, and emulates the run of `tm` from `c`: for every `k`
    there are a block width `2^w`, a band `b`, a window `W` and times, the
    last of them later than `k`, strictly increasing as long as the run of
    `tm` goes on, such that at time `times i` for `i <= k` wolfram23 is in
    state B and the cells right of the head decode by `decodeTM`, on the
    window `W` and on every larger window, to the `i`-th configuration of
    the run (without trailing blanks) whenever that configuration exists.
    Block `k` of the tape re-emulates the first `k` steps with its own width
    and band, as in Smith's construction, so the parameters and the times
    are given per `k`; the decoder reads only the head and the cells to its
    right up to the first 0. -/
theorem wolfram23_infinite (tm : Machine) (hwf : WF tm) (c : Config) (hv : ValidCfg c)
    (hst : c.state < tm.numStates) :
    ∃ t : Nat → Nat, (∀ i, t i < 3) ∧
      (∀ τ, ∃ d, inSteps wolfram23 (istart t) τ = some d ∧
        (d.left = [] → (wolfram23.transition d.state d.head).dir = Dir.R)) ∧
      ∀ k, ∃ (w b W : Nat) (times : Nat → Nat), k < times k ∧
        (∀ i, i < k → (BiTM.nSteps tm c (i + 1)).isSome → times i < times (i + 1)) ∧
        (∀ i ci, i ≤ k → BiTM.nSteps tm c i = some ci → ∃ d,
          inSteps wolfram23 (istart t) (times i) = some d ∧ d.state = 2 ∧
          ∀ W', W ≤ W' → decodeTM tm.numStates (2 ^ w) b (truncI W' d) = some (canon ci)) := by
  -- block `j` emulates the longest run of at most `j` steps
  have hex : ∀ j, ∃ (m : Nat) (bd : BlockData), m ≤ j ∧
      (∀ i, i ≤ j → (BiTM.nSteps tm c i).isSome → i ≤ m) ∧ BlockSpec tm c m bd := by
    intro j
    let P : Nat → Prop := fun i => (BiTM.nSteps tm c i).isSome = true
    have hP0 : P 0 := by simp [P, BiTM.nSteps]
    have hPm : P (Nat.findGreatest P j) := Nat.findGreatest_spec (Nat.zero_le j) hP0
    obtain ⟨cm, hcm⟩ := Option.isSome_iff_exists.mp hPm
    obtain ⟨bd, hbd⟩ := block_exists tm hwf c hv hst _ cm hcm
    exact ⟨Nat.findGreatest P j, bd, Nat.findGreatest_le j,
      fun i hi hPi => Nat.le_findGreatest hi hPi, hbd⟩
  choose m bd hm using hex
  refine ⟨tape bd, tape_lt bd, fun τ => ?_, fun k => ?_⟩
  · obtain ⟨dτ, hdτ, -⟩ := inSteps_valid _ (istart_valid _ (tape_lt bd)) τ
    obtain ⟨-, -, -, times, hkt, -, hleft, -⟩ := stage_infinite tm hwf c hv hst m bd hm τ
    exact ⟨dτ, hdτ, hleft τ hkt dτ hdτ⟩
  · obtain ⟨w, b, W, times, hkt, hmono, -, hdec⟩ := stage_infinite tm hwf c hv hst m bd hm k
    exact ⟨w, b, W, times, hkt, hmono, hdec⟩

end Smith
