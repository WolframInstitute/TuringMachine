/-
  TagSystem.TMToCTS

  PLAN.md target T7 (milestone M4b): a binary Turing machine is simulated
  by a cyclic tag system, with a decoder. The Cocke-Minsky 2-tag system of
  `TagSystem.CockeMinsky` is carried onto the finite alphabet `Fin (1 + 84 S)`
  (`enc`, `dec`; `S` bounds the states of the machine), the tag system is
  carried onto a cyclic tag system by Cook's `tagToCTS` of
  `TagSystem.TagToCTS` (one tag step is `2 (1 + 84 S)` cyclic tag steps), and
  the decoder `decodeCTS` reads the cyclic tag word back: the one-hot blocks
  as tag symbols, the tag symbols as the configuration word
  `A_q x (al x)^m B x (be x)^N`, and the numbers `m`, `N` as tape halves.

  Contents: `Kind.idx`, `enc`, `dec`, `WordOK`, `tagK`, the transport
  `nStepsP_enc`, `cts_of_tag`, `WF`, `tmSys`, `tm_cts_forwardSim`, the
  decoder `decodeCTS`, `decodeCTS_word`, `t7_finite`.
-/

import TagSystem.CockeMinsky
import TagSystem.TagToCTS
import Smith.Doubling

namespace TagSystem

open TM
open BiTM
open Smith

/-! ## The finite alphabet -/

def Kind.idx : Kind → Nat
  | .A => 0 | .al => 1 | .B => 2 | .be => 3
  | .P1 => 4 | .P0 => 5 | .p => 6 | .Q => 7 | .r => 8
  | .E => 9 | .e => 10 | .F => 11 | .f => 12
  | .G => 13 | .g => 14 | .H => 15 | .k => 16
  | .I => 17 | .i => 18 | .J => 19 | .j => 20

def Kind.ofIdx : Nat → Kind
  | 0 => .A | 1 => .al | 2 => .B | 3 => .be
  | 4 => .P1 | 5 => .P0 | 6 => .p | 7 => .Q | 8 => .r
  | 9 => .E | 10 => .e | 11 => .F | 12 => .f
  | 13 => .G | 14 => .g | 15 => .H | 16 => .k
  | 17 => .I | 18 => .i | 19 => .J | _ => .j

theorem Kind.ofIdx_idx (kd : Kind) : Kind.ofIdx kd.idx = kd := by cases kd <;> rfl
theorem Kind.idx_le (kd : Kind) : kd.idx ≤ 20 := by cases kd <;> decide

/-- The two bits of a symbol as a number below 4. -/
def hb (h b : Bool) : Nat := 2 * bit h + bit b

theorem hb_lt (h b : Bool) : hb h b < 4 := by cases h <;> cases b <;> decide

/-- The index of a symbol among `1 + 84 S`. -/
def symIdx (S : Nat) : Sym → Nat
  | none => 0
  | some (kd, q, h, b) => 1 + ((kd.idx * S + q) * 4 + hb h b)

theorem symIdx_lt (S : Nat) (kd : Kind) (q : Nat) (h b : Bool) (hq : q < S) :
    1 + ((kd.idx * S + q) * 4 + hb h b) < 1 + 84 * S := by
  have h1 := Kind.idx_le kd
  have h2 := hb_lt h b
  have : kd.idx * S ≤ 20 * S := Nat.mul_le_mul_right S h1
  omega

/-- The encoding of a symbol. -/
def enc (S : Nat) (s : Sym) : Fin (1 + 84 * S) := ⟨symIdx S s % (1 + 84 * S), Nat.mod_lt _ (by omega)⟩

/-- The decoding of a symbol. -/
def dec (S : Nat) (i : Fin (1 + 84 * S)) : Sym :=
  if i.val = 0 then none
  else
    let n := i.val - 1
    some (Kind.ofIdx (n / 4 / S), n / 4 % S, decide (n % 4 / 2 = 1), decide (n % 4 % 2 = 1))

theorem hb_div (h b : Bool) : decide (hb h b / 2 = 1) = h := by cases h <;> cases b <;> rfl
theorem hb_mod (h b : Bool) : decide (hb h b % 2 = 1) = b := by cases h <;> cases b <;> rfl

theorem dec_enc_X (S : Nat) : dec S (enc S X) = X := by
  simp [dec, enc, symIdx]

theorem dec_enc (S : Nat) (kd : Kind) (q : Nat) (h b : Bool) (hq : q < S) :
    dec S (enc S (some (kd, q, h, b))) = some (kd, q, h, b) := by
  have hS : 0 < S := by omega
  have hlt := symIdx_lt S kd q h b hq
  have hval : (enc S (some (kd, q, h, b))).val = 1 + ((kd.idx * S + q) * 4 + hb h b) := by
    show symIdx S (some (kd, q, h, b)) % (1 + 84 * S) = _
    exact Nat.mod_eq_of_lt hlt
  have h4 : ((kd.idx * S + q) * 4 + hb h b) / 4 = kd.idx * S + q := by
    have := hb_lt h b; omega
  have hm4 : ((kd.idx * S + q) * 4 + hb h b) % 4 = hb h b := by
    have := hb_lt h b; omega
  have hdiv : (kd.idx * S + q) / S = kd.idx := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hq, Nat.zero_add]
  have hmod : (kd.idx * S + q) % S = q := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  simp only [dec, hval, Nat.add_sub_cancel_left, h4, hm4, hdiv, hmod, Kind.ofIdx_idx, hb_div, hb_mod]
  rw [if_neg (by omega)]

/-! ## Symbols with bounded states -/

/-- The state of the symbol is below `S`. -/
def SymOK (S : Nat) : Sym → Prop
  | none => True
  | some (_, q, _, _) => q < S

def WordOK (S : Nat) (w : List Sym) : Prop := ∀ s ∈ w, SymOK S s

@[simp] theorem SymOK_X (S : Nat) : SymOK S X := trivial
@[simp] theorem SymOK_sy (S : Nat) (kd : Kind) (q : Nat) (h b : Bool) :
    SymOK S (sy kd q h b) ↔ q < S := Iff.rfl

theorem forall_mem_pairs2 {P : Sym → Prop} (a b : Sym) (ha : P a) (hb : P b) (m : Nat) :
    ∀ s ∈ pairs2 a b m, P s := by
  induction m with
  | zero => simp
  | succ m ih =>
    intro s hs
    simp only [pairs2_succ, List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · exact ha
    · exact hb
    · exact ih s hs

theorem forall_mem_pad {P : Sym → Prop} (hX : P X) (h : Bool) : ∀ s ∈ pad h, P s := by
  cases h <;> simp [pad, hX]

theorem forall_mem_pairs2_iff (P : Sym → Prop) (a b : Sym) (m : Nat) :
    (∀ s ∈ pairs2 a b m, P s) ↔ (m = 0 ∨ (P a ∧ P b)) := by
  cases m with
  | zero => simp
  | succ m =>
    constructor
    · intro h
      exact Or.inr ⟨h a (by simp), h b (by simp)⟩
    · rintro (h | ⟨ha, hb⟩)
      · omega
      · exact forall_mem_pairs2 a b ha hb _

theorem forall_mem_pad_iff (P : Sym → Prop) (h : Bool) : (∀ s ∈ pad h, P s) ↔ (h = true ∨ P X) := by
  cases h <;> simp [pad]

theorem forall_mem_nil_iff (P : Sym → Prop) : (∀ s ∈ ([] : List Sym), P s) ↔ True := by simp

theorem WordOK_append (S : Nat) (l1 l2 : List Sym) (h1 : WordOK S l1) (h2 : WordOK S l2) :
    WordOK S (l1 ++ l2) := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact h1 s hs
  · exact h2 s hs

theorem WordOK_cword (S q m N : Nat) (hq : q < S) : WordOK S (cword q m N) := by
  intro s hs
  simp only [cword, List.mem_cons, List.mem_append] at hs
  rcases hs with rfl | rfl | hs | rfl | rfl | hs
  · exact hq
  · trivial
  · exact forall_mem_pairs2 (cAl q) X (by simpa [cAl] using hq) trivial m s hs
  · exact hq
  · trivial
  · exact forall_mem_pairs2 (cBe q) X (by simpa [cBe] using hq) trivial N s hs

variable (tm : Machine)

/-- The productions keep the states below `S` when the transitions do. -/
theorem prod_OK (S : Nat) (hn : ∀ q h, q < S → nxt tm q h < S) (s : Sym) (hs : SymOK S s) :
    WordOK S (prod tm s) := by
  cases s with
  | none => simp [WordOK, prod]
  | some t =>
    obtain ⟨kd, q, h, b⟩ := t
    have hq : q < S := hs
    have hn' := hn q h hq
    unfold WordOK
    cases kd <;> simp only [prod] <;> (try split) <;>
      simp only [List.forall_mem_cons, List.forall_mem_append, forall_mem_pairs2_iff,
        forall_mem_pad_iff, forall_mem_nil_iff] <;>
      simp [SymOK, cA, cAl, cB, cBe, cP1, cP0, cp, cQ, cr, cE, ce, cF, cf, cG, cg, cH, ck, cI, ci, cJ,
        cj, sy, hq, hn']

theorem stepP_OK (S : Nat) (hn : ∀ q h, q < S → nxt tm q h < S) (w w' : List Sym)
    (hw : WordOK S w) (hs : stepP (prod tm) w = some w') : WordOK S w' := by
  match w, hs with
  | a :: _ :: rest, hs =>
    obtain rfl := Option.some.inj hs
    exact WordOK_append S _ _ (fun s hs => hw s (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs)))
      (prod_OK tm S hn a (hw a List.mem_cons_self))

/-! ## The tag system on the finite alphabet -/

/-- The Cocke-Minsky tag system with states below `S`, on `Fin (1 + 84 S)`. -/
def tagK (S : Nat) : Tag (1 + 84 * S) where
  productions i := (prod tm (dec S i)).map (enc S)

theorem tagK_productions_enc (S : Nat) (s : Sym) (hs : SymOK S s) :
    (tagK tm S).productions (enc S s) = (prod tm s).map (enc S) := by
  cases s with
  | none => simp [tagK, dec_enc_X]
  | some t =>
    obtain ⟨kd, q, h, b⟩ := t
    simp [tagK, dec_enc S kd q h b hs]

theorem stepP_enc (S : Nat) (w : List Sym) (hw : WordOK S w) :
    stepP (tagK tm S).productions (w.map (enc S)) = (stepP (prod tm) w).map (List.map (enc S)) := by
  match w with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    simp only [List.map_cons, stepP, Option.map_some, List.map_append]
    rw [tagK_productions_enc tm S a (hw a List.mem_cons_self)]

theorem nStepsP_enc (S : Nat) (hn : ∀ q h, q < S → nxt tm q h < S) (k : Nat) :
    ∀ w, WordOK S w →
      nStepsP (tagK tm S).productions (w.map (enc S)) k = (nStepsP (prod tm) w k).map (List.map (enc S)) := by
  induction k with
  | zero => intro w _; rfl
  | succ k ih =>
    intro w hw
    rw [nStepsP_succ, nStepsP_succ, stepP_enc tm S w hw]
    cases hs : stepP (prod tm) w with
    | none => rfl
    | some w' =>
      simp only [Option.map_some, Option.bind_some]
      exact ih w' (stepP_OK tm S hn w w' hw hs)

/-! ## From the tag system to the cyclic tag system -/

theorem Tag.step_eq_stepP {k : Nat} (ts : Tag k) (w : List (Fin k)) : ts.step w = stepP ts.productions w := by
  match w with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- `k` tag steps are `2 K k` cyclic tag steps. -/
theorem cts_of_tag {K : Nat} (ts : Tag K) (hK : K > 0) (k : Nat) :
    ∀ (w w' : List (Fin K)), nStepsP ts.productions w k = some w' →
      (tagToCTS ts hK).nSteps (tagConfigToCTS K w) (2 * K * k) = some (tagConfigToCTS K w') := by
  induction k with
  | zero =>
    intro w w' h
    rw [nStepsP_zero] at h
    obtain rfl := Option.some.inj h
    rfl
  | succ k ih =>
    intro w w' h
    rw [nStepsP_succ] at h
    cases hs : stepP ts.productions w with
    | none => rw [hs] at h; cases h
    | some w1 =>
      rw [hs, Option.bind_some] at h
      have h1 := tagToCTS_simulation ts hK w w1 (by rw [Tag.step_eq_stepP]; exact hs)
      rw [show 2 * K * (k + 1) = 2 * K + 2 * K * k from by ring, CTS.nSteps_add_step, h1,
        Option.bind_some]
      exact ih w1 w' h

/-! ## The machine -/

/-- A well-formed binary machine: from a state below `numStates` reading a
    bit, it writes a bit and moves to a state below `numStates`. -/
def WF (tm : Machine) : Prop :=
  ∀ q, q < tm.numStates → ∀ s, s < 2 →
    (tm.transition q s).write < 2 ∧ (tm.transition q s).nextState < tm.numStates

instance (tm : Machine) : Decidable (WF tm) := by unfold WF; infer_instance

theorem WF_nxt (hwf : WF tm) (q : Nat) (h : Bool) (hq : q < tm.numStates) :
    nxt tm q h < tm.numStates :=
  (hwf q hq (bit h) (by cases h <;> decide)).2

theorem readHead_fst_lt (l : List Nat) (hl : ∀ a ∈ l, a < 2) : (readHead l).1 < 2 := by
  cases l with
  | nil => decide
  | cons a l => exact hl a List.mem_cons_self

theorem readHead_snd_lt (l : List Nat) (hl : ∀ a ∈ l, a < 2) : ∀ a ∈ (readHead l).2, a < 2 := by
  cases l with
  | nil => simp [readHead]
  | cons a l => exact fun x hx => hl x (List.mem_cons_of_mem _ hx)

/-- A step keeps the configuration valid and its state below `numStates`. -/
theorem step_valid (hwf : WF tm) (c c' : Config) (hv : ValidCfg c) (hst : c.state < tm.numStates)
    (hs : BiTM.step tm c = some c') : ValidCfg c' ∧ c'.state < tm.numStates := by
  obtain ⟨q, left, head, right⟩ := c
  obtain ⟨hh, hl, hr⟩ := hv
  simp only at hh hl hr hst
  have hq : q ≠ 0 := by
    intro hq; subst hq; simp [BiTM.step] at hs
  have hw := (hwf q hst head hh).1
  have hn := (hwf q hst head hh).2
  cases hd : (tm.transition q head).dir with
  | R =>
    rw [step_R tm q left head right hq hd] at hs
    obtain rfl := Option.some.inj hs
    refine ⟨⟨readHead_fst_lt right hr, ?_, readHead_snd_lt right hr⟩, hn⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hw
    · exact hl a ha
  | L =>
    rw [step_L tm q left head right hq hd] at hs
    obtain rfl := Option.some.inj hs
    refine ⟨⟨readHead_fst_lt left hl, readHead_snd_lt left hl, ?_⟩, hn⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hw
    · exact hr a ha

/-- The machine as a `StepSys`. -/
def tmSys : StepSys Config := ⟨BiTM.step tm⟩

theorem tmSys_nSteps (c : Config) (n : Nat) : (tmSys tm).nSteps c n = BiTM.nSteps tm c n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [StepSys.nSteps_succ_left]
    show (BiTM.step tm c).bind _ = _
    cases h : BiTM.step tm c with
    | none => simp [BiTM.nSteps, h]
    | some c' => simp [BiTM.nSteps, h, ih]

theorem K_pos (S : Nat) : 1 + 84 * S > 0 := by omega

/-- The encoding of a configuration as a cyclic tag configuration. -/
def ctsOfCfg (S : Nat) (c : Config) : CTSConfig :=
  tagConfigToCTS (1 + 84 * S) ((word c).map (enc S))

/-- T7 as a `ForwardSim`: the cyclic tag system `tagToCTS (tagK tm S)`
    tracks the machine through the encoding of configurations. -/
theorem tm_cts_forwardSim (hwf : WF tm) :
    ForwardSim (tmSys tm) (ctsSys (tagToCTS (tagK tm tm.numStates) (K_pos _)))
      (fun c d => ValidCfg c ∧ c.state < tm.numStates ∧ d = ctsOfCfg tm.numStates c) := by
  rintro c d ⟨hv, hst, rfl⟩ c' hs
  obtain ⟨k, hk, hrun⟩ := tm_step_tag tm c c' hv (hwf c.state hst c.head hv.1).1 hs
  have hn : ∀ q h, q < tm.numStates → nxt tm q h < tm.numStates := fun q h hq => WF_nxt tm hwf q h hq
  have hwOK : WordOK tm.numStates (word c) := WordOK_cword _ _ _ _ hst
  have hrunK := nStepsP_enc tm tm.numStates hn k (word c) hwOK
  rw [hrun, Option.map_some] at hrunK
  have hcts := cts_of_tag (tagK tm tm.numStates) (K_pos _) k _ _ hrunK
  refine ⟨2 * (1 + 84 * tm.numStates) * k, by
    have : 1 ≤ 2 * (1 + 84 * tm.numStates) * k := Nat.mul_pos (by omega) hk
    omega, ctsOfCfg tm.numStates c', ?_, ?_⟩
  · rw [ctsSys_nSteps]; exact hcts
  · obtain ⟨hv', hst'⟩ := step_valid tm hwf c c' hv hst hs
    exact ⟨hv', hst', rfl⟩

/-! ## The decoder -/

/-- The binary digits of a number, least significant first, without
    trailing zeros. -/
def natBits (n : Nat) : List Nat :=
  if h : n = 0 then [] else n % 2 :: natBits (n / 2)
termination_by n
decreasing_by omega

theorem val_natBits (n : Nat) : val (natBits n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natBits]
    split
    · rename_i h; subst h; rfl
    · rename_i h
      rw [val_cons, ih (n / 2) (by omega)]
      omega

theorem natBits_lt (n : Nat) : ∀ a ∈ natBits n, a < 2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natBits]
    split
    · simp
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · omega
      · exact ih (n / 2) (by omega) a ha

/-- The position of the `true` of a one-hot block. -/
def symbolDecodeAux : List Bool → Nat → Option Nat
  | [], _ => none
  | true :: rest, i => if rest.all (fun b => !b) then some i else none
  | false :: rest, i => symbolDecodeAux rest (i + 1)

def symbolDecode (k : Nat) (l : List Bool) : Option (Fin k) :=
  match symbolDecodeAux l 0 with
  | some i => if h : i < k then some ⟨i, h⟩ else none
  | none => none

theorem range_map_beq (k : Nat) : ∀ i, i < k →
    (List.range k).map (fun j => j == i) = List.replicate i false ++ true :: List.replicate (k - i - 1) false := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    rw [List.range_succ, List.map_append, List.map_singleton]
    rcases Nat.lt_or_ge i k with hik | hik
    · rw [ih i hik, show (k == i) = false from by simp; omega, List.append_assoc, List.cons_append,
        ← List.replicate_succ', show k - i - 1 + 1 = k + 1 - i - 1 from by omega]
    · have hi' : i = k := by omega
      subst hi'
      have hrep : (List.range i).map (fun j => j == i) = List.replicate i false := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp, ?_⟩
        intro b hb
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
        rw [List.mem_range] at hj
        simp; omega
      rw [hrep, show (i == i) = true from by simp, show i + 1 - i - 1 = 0 from by omega]
      rfl

theorem symbolDecodeAux_spec (i : Nat) : ∀ (r j : Nat),
    symbolDecodeAux (List.replicate i false ++ true :: List.replicate r false) j = some (j + i) := by
  induction i with
  | zero =>
    intro r j
    simp only [List.replicate_zero, List.nil_append, symbolDecodeAux, Nat.add_zero]
    rw [if_pos]
    rw [List.all_eq_true]
    intro b hb
    rw [List.eq_of_mem_replicate hb]
    rfl
  | succ i ih =>
    intro r j
    rw [List.replicate_succ, List.cons_append]
    show symbolDecodeAux _ (j + 1) = _
    rw [ih r (j + 1)]
    congr 1
    omega

theorem symbolDecode_encode (k : Nat) (a : Fin k) : symbolDecode k (symbolEncode k a) = some a := by
  unfold symbolDecode symbolEncode
  rw [range_map_beq k a.val a.isLt, symbolDecodeAux_spec, Nat.zero_add]
  simp only [a.isLt, dite_true]

/-- The one-hot blocks of a cyclic tag word as tag symbols. -/
def tagWordDecode (k : Nat) (hk : 0 < k) (l : List Bool) : Option (List (Fin k)) :=
  if h : l = [] then some []
  else
    match symbolDecode k (l.take k), tagWordDecode k hk (l.drop k) with
    | some a, some w => some (a :: w)
    | _, _ => none
termination_by l.length
decreasing_by
  have : 0 < l.length := by
    cases l with
    | nil => exact absurd rfl h
    | cons _ _ => simp
  rw [List.length_drop]
  omega

theorem tagWordDecode_encode (k : Nat) (hk : 0 < k) (w : List (Fin k)) :
    tagWordDecode k hk (tagWordEncode k w) = some w := by
  induction w with
  | nil => rw [tagWordDecode]; simp [tagWordEncode]
  | cons a w ih =>
    rw [tagWordDecode]
    have hne : tagWordEncode k (a :: w) ≠ [] := by
      intro h
      have := tagWordEncode_length k (a :: w)
      rw [h] at this
      simp at this
      omega
    rw [dif_neg hne, tagWordEncode_cons, List.take_left' (symbolEncode_length k a),
      List.drop_left' (symbolEncode_length k a), symbolDecode_encode, ih]

/-- The leading pairs `a x` of a word, counted. -/
def countPairs (a : Sym) : List Sym → Nat × List Sym
  | a' :: x' :: rest =>
      if a' = a ∧ x' = X then
        let r := countPairs a rest
        (r.1 + 1, r.2)
      else (0, a' :: x' :: rest)
  | l => (0, l)

theorem countPairs_pairs2 (a : Sym) (m : Nat) (l : List Sym)
    (hl : ∀ a' x' rest, l = a' :: x' :: rest → ¬ (a' = a ∧ x' = X)) :
    countPairs a (pairs2 a X m ++ l) = (m, l) := by
  induction m with
  | zero =>
    rw [pairs2_zero, List.nil_append]
    match l, hl with
    | [], _ => rfl
    | [_], _ => rfl
    | a' :: x' :: rest, hl => simp only [countPairs, if_neg (hl a' x' rest rfl)]
  | succ m ih =>
    rw [pairs2_succ, List.cons_append, List.cons_append]
    simp only [countPairs, and_self, if_true, ih]

def headA : List Sym → Option (Nat × List Sym)
  | some (Kind.A, q, _, _) :: none :: rest => some (q, rest)
  | _ => none

def headB : List Sym → Option (Nat × List Sym)
  | some (Kind.B, q, _, _) :: none :: rest => some (q, rest)
  | _ => none

@[simp] theorem headA_cons (q : Nat) (rest : List Sym) : headA (cA q :: X :: rest) = some (q, rest) := rfl
@[simp] theorem headB_cons (q : Nat) (rest : List Sym) : headB (cB q :: X :: rest) = some (q, rest) := rfl

/-- The state and the two numbers of a configuration word. -/
def parseWord (w : List Sym) : Option (Nat × Nat × Nat) :=
  match headA w with
  | none => none
  | some (q, r0) =>
    let r1 := countPairs (cAl q) r0
    match headB r1.2 with
    | none => none
    | some (q', r2) =>
      if q' = q then
        let r3 := countPairs (cBe q) r2
        if r3.2 = [] then some (q, r1.1, r3.1) else none
      else none

theorem parseWord_cword (q m N : Nat) : parseWord (cword q m N) = some (q, m, N) := by
  have h1 : countPairs (cAl q) (pairs2 (cAl q) X m ++ cB q :: X :: pairs2 (cBe q) X N)
      = (m, cB q :: X :: pairs2 (cBe q) X N) := by
    apply countPairs_pairs2
    intro a' x' rest h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [cB, cAl, sy]
  have h2 : countPairs (cBe q) (pairs2 (cBe q) X N) = (N, []) := by
    rw [pairs2_eq_append_nil]
    exact countPairs_pairs2 _ _ _ (by intro a' x' rest h; cases h)
  simp only [parseWord, cword, headA_cons, h1, headB_cons, h2, if_true]

/-- The configuration of the state and the two numbers: the scanned cell is
    the lowest bit of the right number. -/
def cfgOfNums (q m N : Nat) : Config := ⟨q, natBits m, N % 2, natBits (N / 2)⟩

/-- A configuration without trailing blanks on either side. -/
def canon (c : Config) : Config := ⟨c.state, natBits (val c.left), c.head, natBits (val c.right)⟩

def decodeWord (w : List Sym) : Option Config :=
  (parseWord w).map (fun t => cfgOfNums t.1 t.2.1 t.2.2)

/-- The decoder of the cyclic tag configuration: the one-hot blocks as tag
    symbols, the tag symbols as a configuration word, its numbers as the
    tape halves. -/
def decodeCTS (S : Nat) (d : CTSConfig) : Option Config :=
  (tagWordDecode (1 + 84 * S) (K_pos S) d.data).bind (fun w => decodeWord (w.map (dec S)))

theorem map_dec_enc (S : Nat) (w : List Sym) (hw : WordOK S w) : (w.map (enc S)).map (dec S) = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  apply List.map_congr_left
  intro s hs
  cases s with
  | none => exact dec_enc_X S
  | some t =>
    obtain ⟨kd, q, h, b⟩ := t
    exact dec_enc S kd q h b (hw _ hs)

theorem decodeCTS_word (S : Nat) (c : Config) (hv : ValidCfg c) (hst : c.state < S) :
    decodeCTS S (ctsOfCfg S c) = some (canon c) := by
  unfold decodeCTS ctsOfCfg tagConfigToCTS word
  simp only [tagWordDecode_encode, Option.bind_some, map_dec_enc S _ (WordOK_cword S _ _ _ hst)]
  unfold decodeWord
  rw [parseWord_cword, Option.map_some]
  have hh := hv.1
  simp only [cfgOfNums, canon]
  have h1 : (c.head + 2 * val c.right) % 2 = c.head := by omega
  have h2 : (c.head + 2 * val c.right) / 2 = val c.right := by omega
  rw [h1, h2]

/-- T7 in finite form: the cyclic tag system `tagToCTS (tagK tm S)` tracks
    every run of the well-formed binary machine from a valid configuration,
    at strictly increasing times, and `decodeCTS` reads the configurations
    back up to trailing blanks. -/
theorem t7_finite (hwf : WF tm) (c : Config) (hv : ValidCfg c) (hst : c.state < tm.numStates)
    (n : Nat) (c' : Config) (hrun : BiTM.nSteps tm c n = some c') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ i, i < n → times i < times (i + 1)) ∧
      ∀ i, i ≤ n → ∃ ci di, BiTM.nSteps tm c i = some ci ∧
        (tagToCTS (tagK tm tm.numStates) (K_pos _)).nSteps (ctsOfCfg tm.numStates c) (times i)
          = some di ∧
        decodeCTS tm.numStates di = some (canon ci) := by
  obtain ⟨times, h0, hmono, htr⟩ := ForwardSim_nSteps (tm_cts_forwardSim tm hwf) n c
    (ctsOfCfg tm.numStates c) ⟨hv, hst, rfl⟩ c' (by rw [tmSys_nSteps]; exact hrun)
  refine ⟨times, h0, hmono, fun i hi => ?_⟩
  obtain ⟨ci, di, hci, hdi, hvi, hsti, rfl⟩ := htr i hi
  exact ⟨ci, _, by rw [← tmSys_nSteps]; exact hci, by rw [← ctsSys_nSteps]; exact hdi,
    decodeCTS_word _ ci hvi hsti⟩

/-! ## The tag-level schedule -/

/-- The tag system on the finite alphabet as a `StepSys`. -/
def tagSysK (S : Nat) : StepSys (List (Fin (1 + 84 * S))) := ⟨stepP (tagK tm S).productions⟩

theorem tagSysK_nSteps (S : Nat) (w : List (Fin (1 + 84 * S))) (n : Nat) :
    (tagSysK tm S).nSteps w n = nStepsP (tagK tm S).productions w n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [StepSys.nSteps_succ_left, nStepsP_succ]
    show (stepP (tagK tm S).productions w).bind _ = _
    cases stepP (tagK tm S).productions w with
    | none => rfl
    | some w' => simp only [Option.bind_some]; exact ih w'

/-- T7 at the tag level: the tag system `tagK tm S` tracks the machine
    through the encoding of configurations. -/
theorem tm_tag_forwardSim (hwf : WF tm) :
    ForwardSim (tmSys tm) (tagSysK tm tm.numStates)
      (fun c w => ValidCfg c ∧ c.state < tm.numStates ∧ w = (word c).map (enc tm.numStates)) := by
  rintro c w ⟨hv, hst, rfl⟩ c' hs
  obtain ⟨k, hk, hrun⟩ := tm_step_tag tm c c' hv (hwf c.state hst c.head hv.1).1 hs
  have hn : ∀ q h, q < tm.numStates → nxt tm q h < tm.numStates := fun q h hq => WF_nxt tm hwf q h hq
  have hrunK := nStepsP_enc tm tm.numStates hn k (word c) (WordOK_cword _ _ _ _ hst)
  rw [hrun, Option.map_some] at hrunK
  obtain ⟨hv', hst'⟩ := step_valid tm hwf c c' hv hst hs
  exact ⟨k, hk, _, by rw [tagSysK_nSteps]; exact hrunK, hv', hst', rfl⟩

/-- The configuration word is never short: the tag system does not halt on it. -/
theorem length_word (c : Config) : 4 ≤ (word c).length := by
  simp [word, cword]; omega

end TagSystem
