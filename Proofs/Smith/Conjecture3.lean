/-
  Smith.Conjecture3

  PLAN.md target T3, first half, link D (milestone M5): System 3 emulates
  System 4 (TM23Proof.pdf p. 10-15, "Conjecture 4 implies conjecture 3").

  A System 3 tape standing for a System 4 tape is described by an abstract
  configuration `AC`: the items left of the head (nearest first), the items
  right of it, the left end `0^m 2 2 1^t`, the System 4 state, and the
  focus, which says what the head is on. Both the System 4 configuration
  (`AC.to4`) and the System 3 configuration (`AC.toL`) are computed from
  it, and `Rep3` says that a pair of configurations comes from an `AC`
  that satisfies the side conditions `AC.OK`:

    * every set of System 4 is a block of `N = 2^w` cells, 1s and 2s, whose
      parity set on the next `h + 1` scans is the set (`Decodes`), `h`
      being the number of System 4 steps left;
    * every star is a 0 that stands in the place of the last cell of the
      set to its left when the star is left of the head (or at the head in
      state A or C), and in the place of the first cell of the set to its
      right when the star is right of the head (or at the head in state B
      or C); the replaced cell is a 2 (`lastTrue`, `firstTrue`);
    * the left end of the tape is `0^m 2 2 1^t`, one 0 being turned into a
      2 by every return of System 4's head to its leftmost element;
    * the head: on any cell of the active block in state A (`Focus.setA`,
      the block given as a zipper); on its first cell in state B or C
      (`Focus.setB`); right after System 4's rule 5, on its second cell in
      state B with the block decoding to the set with 1 toggled
      (`Focus.setT`; the skipped first cell, a 2, is what turns "toggle 1,
      then decrement" into a scan); on a star's 0 in state A or B; on the
      second of the two 0s of a star active in state C, in state A; and
      past the tape on the closing 1 when System 4's head has left its
      tape (`Focus.off`).

  System 3 matches each System 4 step by a run: rule 1 by a walk to the
  left of `p + 1` steps, or `p + 2t + 6` at the left end (the turn also
  rewrites the left end `2 2 1^t` into `2 1 1^t`); rules 2, 4, 5 by one
  step; rule 3 by a scan of `N` cells, or `N - 1` after rule 5.

  Contents: `Decodes`, `Item`, `renderL`, `renderR`, `leftEndRev`, `Focus`,
  `AC`, `AC.toL`, `AC.to4`, `AC.OK`, `Rep3`, the parity lemmas of a scan,
  the run lemmas for each rule, `ac_step`, `sys4_sys3_forwardSim`.
-/

import Smith.System3Runs
import Smith.LoopFree
import Smith.Conjecture4

namespace Smith

open TM
open BiTM
open LState

/-- The block `x` decodes to the set `S` on its next `k` scans. -/
def Decodes (x : Bits) (S : List Int) (k : Nat) : Prop :=
  ∀ j : Nat, j < k → parAt x j = decide ((j : Int) ∈ S)

instance (x : Bits) (S : List Int) (k : Nat) : Decidable (Decodes x S k) := by
  unfold Decodes; infer_instance

/-- A tape element with its block: a set with its System 4 set, or a star. -/
inductive Item : Type
  | set (x : Bits) (S : List Int) : Item
  | star : Item

/-- The System 4 element of an item. -/
def Item.toElem : Item → System4Elem
  | Item.set _ S => System4Elem.set S
  | Item.star => System4Elem.star

/-- An item is sound for width `N` and `k` scans: a block of width `N`
    decoding to its set, which has no duplicates. -/
def ItemOK (N k : Nat) : Item → Prop
  | Item.set x S => x.length = N ∧ S.Nodup ∧ Decodes x S k
  | Item.star => True

/-- The cells of the items right of the head, left to right: a set gives
    its block, without its first cell when a star precedes it; a star
    gives a 0. -/
def renderR : Bool → List Item → List (Fin 3)
  | _, [] => []
  | false, Item.set x _ :: rest => ofBits x ++ renderR false rest
  | true, Item.set x _ :: rest => (ofBits x).tail ++ renderR false rest
  | _, Item.star :: rest => 0 :: renderR true rest

/-- The cells of the items left of the head, nearest first (the items
    are given nearest first too): a set gives its block reversed, without
    its last cell when a star follows it; a star gives a 0. -/
def renderL : Bool → List Item → List (Fin 3)
  | _, [] => []
  | false, Item.set x _ :: rest => ofBits x.reverse ++ renderL false rest
  | true, Item.set x _ :: rest => (ofBits x.reverse).tail ++ renderL false rest
  | _, Item.star :: rest => 0 :: renderL true rest

/-- The left end of the tape, nearest the head first: `1^t 2 2 0^m`. -/
def leftEndRev (m t : Nat) : List (Fin 3) :=
  List.replicate t 1 ++ [2, 2] ++ List.replicate m 0

/-- The left end of the tape beyond the items: the `0^m 2 2 1^t` of the finite
    construction, which turns the head round once per zero; or arbitrary
    cells, never reached because System 4 never turns at its left end
    within the budget (the concatenated construction of `Smith.Infinite`,
    whose blocks are guarded by stars). -/
inductive LeftEnd : Type
  | zeros (m t : Nat) : LeftEnd
  | junk (L : List (Fin 3)) : LeftEnd

/-- The cells of the left end, nearest the head first. -/
def LeftEnd.render : LeftEnd → List (Fin 3)
  | LeftEnd.zeros m t => leftEndRev m t
  | LeftEnd.junk L => L

/-- Whether the left end is junk. -/
def LeftEnd.isJunk : LeftEnd → Bool
  | LeftEnd.zeros _ _ => false
  | LeftEnd.junk _ => true

/-- The right end of the tape beyond the items: the closing `1` of the
    finite construction, on which the head stops when System 4 leaves its
    tape; or a `0` followed by arbitrary cells (the next block of the
    concatenated construction), on which the head lands as on a star. -/
inductive Closing : Type
  | one : Closing
  | zero (Rc : List (Fin 3)) : Closing

/-- The cells of the right end, nearest the head first. -/
def Closing.render : Closing → List (Fin 3)
  | Closing.one => [1]
  | Closing.zero Rc => 0 :: Rc

/-- `SafeC h c`: within the next `h` System 4 steps the head is on the
    leftmost element only in state C. Rule 1 at the leftmost element (the
    turn) and rule 4 there (stuck) are the only steps that would look at
    what lies left of the tape; rules 2, 3 and 5 do not. -/
def SafeC (h : Nat) (c : System4Config) : Prop :=
  ∀ j, j ≤ h → ∀ c', System4.nSteps c j = some c' → c'.active ≠ 0 ∨ c'.state = System4State.C

theorem SafeC_step (h : Nat) (c c' : System4Config) (hs : System4.step c = some c')
    (hS : SafeC (h + 1) c) : SafeC h c' := by
  intro j hj c'' hc''
  refine hS (j + 1) (by omega) c'' ?_
  rw [System4.nSteps_succ, hs, Option.bind_some]
  exact hc''

theorem SafeC_now (h : Nat) (c : System4Config) (hS : SafeC h c) :
    c.active ≠ 0 ∨ c.state = System4State.C :=
  hS 0 (Nat.zero_le _) c rfl

theorem SafeC_mono (h h' : Nat) (c : System4Config) (hS : SafeC h c) (hh : h' ≤ h) : SafeC h' c :=
  fun j hj => hS j (le_trans hj hh)

/-- The condition on the left end with `h` System 4 steps left: enough
    zeros for the turns, or no turn at all. -/
def LeftEnd.OK (h : Nat) (c4 : System4Config) : LeftEnd → Prop
  | LeftEnd.zeros m t => h ≤ m ∧ 1 ≤ t
  | LeftEnd.junk _ => SafeC h c4

theorem LeftEnd.OK_step (le : LeftEnd) (h : Nat) (c4 c4' : System4Config)
    (hs : System4.step c4 = some c4') (hOK : le.OK (h + 1) c4) : le.OK h c4' := by
  cases le with
  | zeros m t => exact ⟨by have := hOK.1; omega, hOK.2⟩
  | junk L => exact SafeC_step h c4 c4' hs hOK

/-- The first bit of a block. -/
def firstTrue (x : Bits) : Prop := x.head? = some true

/-- The last bit of a block. -/
def lastTrue (x : Bits) : Prop := x.getLast? = some true

instance (x : Bits) : Decidable (firstTrue x) := by unfold firstTrue; infer_instance
instance (x : Bits) : Decidable (lastTrue x) := by unfold lastTrue; infer_instance

/-- The items left of the head, nearest first: a star stands in the place
    of the last cell of the set beyond it, which is a 2; the leftmost item
    is a set, or, when the left end is junk (`j`), a star that is never
    reached. -/
def LeftOK (j : Bool) : List Item → Prop
  | [] => True
  | Item.star :: Item.set x S :: rest => lastTrue x ∧ LeftOK j (Item.set x S :: rest)
  | Item.star :: [] => j = true
  | Item.star :: Item.star :: _ => False
  | Item.set _ _ :: rest => LeftOK j rest


/-- The items right of the head, left to right: a star stands in the place
    of the first cell of the set after it, which is a 2; the last item is
    a set. -/
def RightOK : List Item → Prop
  | [] => True
  | Item.star :: Item.set x S :: rest => firstTrue x ∧ RightOK (Item.set x S :: rest)
  | Item.star :: _ => False
  | Item.set _ _ :: rest => RightOK rest

/-- The first item is a set. -/
def HeadSet : List Item → Prop
  | Item.set _ _ :: _ => True
  | _ => False

/-- The first item is a set with last bit true. -/
def HeadLastTrue : List Item → Prop
  | Item.set x _ :: _ => lastTrue x
  | _ => False

/-- The first item is a set with first bit true. -/
def HeadFirstTrue : List Item → Prop
  | Item.set x _ :: _ => firstTrue x
  | _ => False

/-- The star at the head stands in the place of the last cell of the set
    left of it, or, with a junk left end, nothing is left of it. -/
def LeftLast (j : Bool) (ls : List Item) : Prop := HeadLastTrue ls ∨ (ls = [] ∧ j = true)

/-- What the head is on. -/
inductive Focus : Type
  /-- State A, on the cell `b` of the block `xl.reverse ++ b :: xr`. -/
  | setA (xl : Bits) (b : Bool) (xr : Bits) (S : List Int) : Focus
  /-- State B or C, on the first cell of the block `x0 :: x'`. -/
  | setB (x0 : Bool) (x' : Bits) (S : List Int) : Focus
  /-- State C right after rule 5: on the second cell of the block
      `true :: x1 :: x'`, in System 3's state B. -/
  | setT (x1 : Bool) (x' : Bits) (S : List Int) : Focus
  /-- On a star. -/
  | star : Focus
  /-- Past the right end of the tape. -/
  | off : Focus

/-- An abstract configuration. -/
structure AC where
  ls : List Item
  rs : List Item
  le : LeftEnd
  rc : Closing
  st : System4State
  foc : Focus

/-- System 4's states as System 3's. -/
def st3 : System4State → LState
  | System4State.A => A
  | System4State.B => B
  | System4State.C => C

/-- The System 4 configuration of an abstract configuration. -/
def AC.to4 (a : AC) : System4Config :=
  match a.foc with
  | Focus.setA _ _ _ S =>
      ⟨a.ls.reverse.map Item.toElem ++ System4Elem.set S :: a.rs.map Item.toElem,
       (a.ls.reverse.map Item.toElem).length, a.st⟩
  | Focus.setB _ _ S =>
      ⟨a.ls.reverse.map Item.toElem ++ System4Elem.set S :: a.rs.map Item.toElem,
       (a.ls.reverse.map Item.toElem).length, a.st⟩
  | Focus.setT _ _ S =>
      ⟨a.ls.reverse.map Item.toElem ++ System4Elem.set S :: a.rs.map Item.toElem,
       (a.ls.reverse.map Item.toElem).length, a.st⟩
  | Focus.star =>
      ⟨a.ls.reverse.map Item.toElem ++ System4Elem.star :: a.rs.map Item.toElem,
       (a.ls.reverse.map Item.toElem).length, a.st⟩
  | Focus.off =>
      ⟨a.ls.reverse.map Item.toElem, (a.ls.reverse.map Item.toElem).length, a.st⟩

/-- The System 3 configuration of an abstract configuration. -/
def AC.toL (a : AC) : LConfig :=
  match a.foc with
  | Focus.setA xl b xr _ =>
      ⟨ofBits xl ++ renderL false a.ls ++ a.le.render, toCell b,
       ofBits xr ++ renderR false a.rs ++ a.rc.render, A⟩
  | Focus.setB x0 x' _ =>
      ⟨renderL false a.ls ++ a.le.render, toCell x0,
       ofBits x' ++ renderR false a.rs ++ a.rc.render, st3 a.st⟩
  | Focus.setT x1 x' _ =>
      ⟨2 :: (renderL false a.ls ++ a.le.render), toCell x1,
       ofBits x' ++ renderR false a.rs ++ a.rc.render, B⟩
  | Focus.star =>
      match a.st with
      | System4State.A =>
          ⟨renderL true a.ls ++ a.le.render, 0, renderR false a.rs ++ a.rc.render, A⟩
      | System4State.B =>
          ⟨renderL false a.ls ++ a.le.render, 0, renderR true a.rs ++ a.rc.render, B⟩
      | System4State.C =>
          ⟨0 :: (renderL true a.ls ++ a.le.render), 0, renderR true a.rs ++ a.rc.render, A⟩
  | Focus.off =>
      match a.rc with
      | Closing.one => ⟨renderL false a.ls ++ a.le.render, 1, [], st3 a.st⟩
      | Closing.zero Rc =>
          match a.st with
          | System4State.C => ⟨0 :: (renderL true a.ls ++ a.le.render), 0, Rc, A⟩
          | _ => ⟨renderL false a.ls ++ a.le.render, 0, Rc, B⟩

/-- The side conditions on the focus. -/
def FocusOK (N k : Nat) (j : Bool) (st : System4State) (ls rs : List Item) : Focus → Prop
  | Focus.setA xl b xr S => st = System4State.A ∧ ItemOK N k (Item.set (xl.reverse ++ b :: xr) S)
  | Focus.setB x0 x' S => st ≠ System4State.A ∧ ItemOK N k (Item.set (x0 :: x') S)
  | Focus.setT x1 x' S =>
      st = System4State.C ∧ S.Nodup ∧ (true :: x1 :: x').length = N ∧
        Decodes (true :: x1 :: x') (xorInsert 1 S) k
  | Focus.star =>
      match st with
      | System4State.A => HeadLastTrue ls ∧ HeadSet rs
      | System4State.B => HeadSet ls ∧ HeadFirstTrue rs
      | System4State.C => LeftLast j ls ∧ HeadFirstTrue rs
  | Focus.off => True

/-- The side conditions of an abstract configuration, for width `2^w` and
    `h` System 4 steps left. -/
def AC.OK (w h : Nat) (a : AC) : Prop :=
  h + 3 ≤ 2 ^ w ∧ a.le.OK h a.to4 ∧
  (∀ it ∈ a.ls, ItemOK (2 ^ w) (h + 1) it) ∧ (∀ it ∈ a.rs, ItemOK (2 ^ w) (h + 1) it) ∧
  LeftOK a.le.isJunk a.ls ∧ RightOK a.rs ∧ FocusOK (2 ^ w) (h + 1) a.le.isJunk a.st a.ls a.rs a.foc

/-- The relation of link D: the System 3 configuration `c3` stands for the
    System 4 configuration `c4` with blocks of width `2^w`, `h` System 4
    steps left, and the right end `rc` beyond the items. -/
def Rep3 (rc : Closing) (c3 : LConfig) (c4 : System4Config) (w h : Nat) : Prop :=
  ∃ a : AC, a.rc = rc ∧ a.OK w h ∧ c3 = a.toL ∧ c4 = a.to4

/-! ## Rendering lemmas -/

@[simp] theorem renderR_nil (b : Bool) : renderR b [] = [] := by cases b <;> rfl
@[simp] theorem renderR_set_false (x : Bits) (S : List Int) (rest : List Item) :
    renderR false (Item.set x S :: rest) = ofBits x ++ renderR false rest := rfl
@[simp] theorem renderR_set_true (x : Bits) (S : List Int) (rest : List Item) :
    renderR true (Item.set x S :: rest) = (ofBits x).tail ++ renderR false rest := rfl
@[simp] theorem renderR_star (b : Bool) (rest : List Item) :
    renderR b (Item.star :: rest) = 0 :: renderR true rest := by cases b <;> rfl
@[simp] theorem renderL_nil (b : Bool) : renderL b [] = [] := by cases b <;> rfl
@[simp] theorem renderL_set_false (x : Bits) (S : List Int) (rest : List Item) :
    renderL false (Item.set x S :: rest) = ofBits x.reverse ++ renderL false rest := rfl
@[simp] theorem renderL_set_true (x : Bits) (S : List Int) (rest : List Item) :
    renderL true (Item.set x S :: rest) = (ofBits x.reverse).tail ++ renderL false rest := rfl
@[simp] theorem renderL_star (b : Bool) (rest : List Item) :
    renderL b (Item.star :: rest) = 0 :: renderL true rest := by cases b <;> rfl

theorem ofBits_append (x y : Bits) : ofBits (x ++ y) = ofBits x ++ ofBits y := List.map_append ..
theorem ofBits_reverse (x : Bits) : ofBits x.reverse = (ofBits x).reverse := List.map_reverse ..
theorem ofBits_replicate_false (n : Nat) : ofBits (List.replicate n false) = List.replicate n 1 := by
  simp [ofBits]

theorem ofBits_ne_zero (x : Bits) : ∀ c ∈ ofBits x, c ≠ 0 := by
  intro c hc
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
  exact toCell_ne_zero b

theorem firstTrue_cons (x : Bits) (h : firstTrue x) : ∃ x', x = true :: x' := by
  cases x with
  | nil => exact absurd h (by simp [firstTrue])
  | cons a x' => exact ⟨x', by simp [firstTrue] at h; rw [h]⟩

theorem lastTrue_reverse (x : Bits) (h : lastTrue x) : ∃ xl, x.reverse = true :: xl := by
  have h' : x.reverse.head? = some true := by
    rw [List.head?_reverse]; exact h
  cases hx : x.reverse with
  | nil => rw [hx] at h'; simp at h'
  | cons a xl => rw [hx] at h'; simp at h'; exact ⟨xl, by rw [h']⟩

/-- A star at the head in state B or C, or right of a set: the 0 of the
    star is the first cell of the set after it. -/
theorem renderR_of_headFirstTrue (rs : List Item) (h : HeadFirstTrue rs) :
    2 :: renderR true rs = renderR false rs := by
  match rs, h with
  | Item.set x S :: rest, h =>
    obtain ⟨x', rfl⟩ := firstTrue_cons x h
    rfl

/-- A star at the head in state A or C, or left of a set: the 0 of the
    star is the last cell of the set before it. -/
theorem renderL_of_headLastTrue (ls : List Item) (h : HeadLastTrue ls) :
    2 :: renderL true ls = renderL false ls := by
  match ls, h with
  | Item.set x S :: rest, h =>
    obtain ⟨xl, hx⟩ := lastTrue_reverse x h
    simp only [renderL_set_true, renderL_set_false, hx, ofBits_cons, toCell_true, List.tail_cons,
      List.cons_append]

theorem LeftOK_star (j : Bool) (ls : List Item) (h : LeftOK j (Item.star :: ls)) :
    (HeadLastTrue ls ∧ LeftOK j ls) ∨ (ls = [] ∧ j = true) := by
  match ls, h with
  | [], h => exact Or.inr ⟨rfl, h⟩
  | Item.set x S :: rest, h => exact Or.inl ⟨h.1, h.2⟩

theorem LeftOK_of_leftLast (j : Bool) (ls : List Item) (hL : LeftOK j ls) (h : LeftLast j ls) :
    LeftOK j (Item.star :: ls) := by
  rcases h with h | ⟨rfl, rfl⟩
  · match ls, h, hL with
    | Item.set x S :: rest, h, hL => exact ⟨h, hL⟩
  · rfl

theorem RightOK_star (rs : List Item) (h : RightOK (Item.star :: rs)) : HeadFirstTrue rs ∧ RightOK rs := by
  match rs, h with
  | Item.set x S :: rest, h => exact ⟨h.1, h.2⟩

theorem LeftOK_set (j : Bool) (x : Bits) (S : List Int) (ls : List Item) :
    LeftOK j (Item.set x S :: ls) ↔ LeftOK j ls := by
  cases ls with
  | nil => rfl
  | cons it rest => cases it <;> rfl

theorem RightOK_set (x : Bits) (S : List Int) (rs : List Item) :
    RightOK (Item.set x S :: rs) ↔ RightOK rs := by
  cases rs with
  | nil => rfl
  | cons it rest => cases it <;> rfl

theorem HeadSet_of_lastTrue (ls : List Item) (h : HeadLastTrue ls) : HeadSet ls := by
  match ls, h with
  | Item.set x S :: rest, _ => trivial

theorem HeadSet_of_firstTrue (rs : List Item) (h : HeadFirstTrue rs) : HeadSet rs := by
  match rs, h with
  | Item.set x S :: rest, _ => trivial

/-! ## The parity side of a scan -/

theorem Decodes_mono (x : Bits) (S : List Int) (j k : Nat) (h : Decodes x S k) (hjk : j ≤ k) :
    Decodes x S j := fun i hi => h i (by omega)

theorem ItemOK_mono (N j k : Nat) (it : Item) (h : ItemOK N k it) (hjk : j ≤ k) : ItemOK N j it := by
  cases it with
  | star => trivial
  | set x S => exact ⟨h.1, h.2.1, Decodes_mono x S j k h.2.2 hjk⟩

theorem parAt_zero (x : Bits) : parAt x 0 = parity x := rfl

/-- The first scan decides membership of 0. -/
theorem Decodes_parity (x : Bits) (S : List Int) (k : Nat) (h : Decodes x S (k + 1)) :
    parity x = decide ((0 : Int) ∈ S) := by
  have := h 0 (by omega)
  rw [parAt_zero] at this
  simpa using this

/-- After a scan in state B the block decodes to the decremented set. -/
theorem Decodes_T (x : Bits) (S : List Int) (hS : S.Nodup) (k : Nat) (h : Decodes x S (k + 1)) :
    Decodes (T x) (decr S) k := by
  intro j hj
  rw [parAt_T, h (j + 1) (by omega), decide_eq_decide, decr_mem S hS]
  push_cast
  constructor
  · intro hm; exact ⟨hm, by omega⟩
  · exact fun hm => hm.1

/-- `row 0` has parity only at scan 0 within the window. -/
theorem parAt_unit (w j : Nat) (hj : j < 2 ^ w) : parAt (unit (2 ^ w)) j = decide (j = 0) :=
  parAt_row w 0 j Nat.one_le_two_pow hj

/-- Toggling the first bit toggles the parity set at 0 only. -/
theorem parAt_toggle_first (w : Nat) (a : Bool) (x : Bits) (hx : (a :: x).length = 2 ^ w) (j : Nat)
    (hj : j < 2 ^ w) : parAt ((!a) :: x) j = (parAt (a :: x) j ^^ decide (j = 0)) := by
  have hxor : (!a) :: x = xorB (a :: x) (unit (2 ^ w)) := by
    have hl : x.length = 2 ^ w - 1 := by simp at hx; omega
    unfold unit
    rw [xorB_cons, ← hl]
    have : xorB x (zeros x.length) = x := xorB_zeros_right x
    rw [this]
    cases a <;> rfl
  rw [hxor, parAt_xor _ _ (by rw [hx, length_unit _ Nat.one_le_two_pow]), parAt_unit w j hj]

/-- After a scan in state C the block decodes to the decremented set as
    well (Corollary 0): the toggle of the first bit is invisible after the
    first scan. -/
theorem Decodes_scanC (w : Nat) (a : Bool) (x : Bits) (hx : (a :: x).length = 2 ^ w)
    (S : List Int) (hS : S.Nodup) (k : Nat) (hk : k + 1 < 2 ^ w)
    (h : Decodes (a :: x) S (k + 1)) : Decodes (scanFrom true (a :: x)) (decr S) k := by
  rw [scanC_eq_T_toggle]
  intro j hj
  rw [parAt_T, parAt_toggle_first w a x hx (j + 1) (by omega), h (j + 1) (by omega)]
  have h0 : decide (j + 1 = 0) = false := by simp
  rw [h0, Bool.xor_false, decide_eq_decide, decr_mem S hS]
  push_cast
  constructor
  · intro hm; exact ⟨hm, by omega⟩
  · exact fun hm => hm.1

/-- The skipped-cell scan after rule 5: the block with its first bit kept
    and the rest scanned from state B decodes to the decremented set when
    the block decoded to the set with 1 toggled. -/
theorem Decodes_transient (w : Nat) (x : Bits) (hx : (true :: x).length = 2 ^ w)
    (S : List Int) (hS : S.Nodup) (k : Nat) (hk : k + 1 < 2 ^ w)
    (h : Decodes (true :: x) (xorInsert 1 S) (k + 1)) :
    Decodes (true :: scanFrom false x) (decr S) k := by
  have e1 : true :: scanFrom false x = (!false) :: scanFrom false x := rfl
  have e2 : false :: scanFrom false x = T (false :: x) := by simp [T, scanFrom]
  have hl : (false :: scanFrom false x).length = 2 ^ w := by simp at hx ⊢; omega
  intro j hj
  rw [e1, parAt_toggle_first w false (scanFrom false x) hl j (by omega), e2, parAt_T,
    show false :: x = (!true) :: x from rfl, parAt_toggle_first w true x hx (j + 1) (by omega),
    h (j + 1) (by omega)]
  have h0 : decide (j + 1 = 0) = false := by simp
  rw [h0, Bool.xor_false]
  have hm := xorInsert_mem_iff 1 S hS ((j + 1 : Nat) : Int)
  have hd := decr_mem S hS (j : Int)
  have hc : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
  rw [← hc] at hd
  have hne : (((j + 1 : Nat) : Int) = 1) ↔ j = 0 := by constructor <;> intro hh <;> omega
  by_cases hj0 : j = 0
  · subst hj0
    have h1eq : ((0 + 1 : Nat) : Int) = 1 := hne.mpr rfl
    rw [decide_eq_true (Eq.refl (0 : Nat)), Bool.xor_true]
    by_cases h1 : (1 : Int) ∈ S
    · have hmem : ((0 + 1 : Nat) : Int) ∈ S := by rw [h1eq]; exact h1
      have hA : ((0 + 1 : Nat) : Int) ∉ xorInsert 1 S := fun hh => (hm.mp hh).mp hmem h1eq
      have hD : ((0 : Nat) : Int) ∈ decr S := hd.mpr ⟨hmem, by omega⟩
      rw [decide_eq_false hA, decide_eq_true hD]; rfl
    · have hA : ((0 + 1 : Nat) : Int) ∈ xorInsert 1 S :=
        hm.mpr ⟨fun hh => absurd (by rw [h1eq] at hh; exact hh) h1, fun hh => absurd h1eq hh⟩
      have hD : ((0 : Nat) : Int) ∉ decr S := fun hh => h1 (by rw [← h1eq]; exact (hd.mp hh).1)
      rw [decide_eq_true hA, decide_eq_false hD]; rfl
  · have h1ne : ((j + 1 : Nat) : Int) ≠ 1 := fun hh => hj0 (hne.mp hh)
    rw [decide_eq_false hj0, Bool.xor_false, decide_eq_decide, hd, hm]
    constructor
    · intro hh; exact ⟨hh.mpr h1ne, by omega⟩
    · exact fun hh => ⟨fun _ => h1ne, fun _ => hh.1⟩

/-- Toggling 1 twice changes no membership. -/
theorem Decodes_xorInsert_twice (x : Bits) (S : List Int) (hS : S.Nodup) (k : Nat)
    (h : Decodes x S k) : Decodes x (xorInsert 1 (xorInsert 1 S)) k := by
  intro j hj
  rw [h j hj, decide_eq_decide, xorInsert_mem_iff 1 _ (xorInsert_nodup 1 S hS),
    xorInsert_mem_iff 1 S hS]
  by_cases h1 : (j : Int) = 1 <;> simp [h1]

/-- The parity of a transient block: 0 is in the set with 1 toggled iff it
    is in the set. -/
theorem Decodes_transient_parity (x : Bits) (S : List Int) (k : Nat)
    (h : Decodes (true :: x) (xorInsert 1 S) (k + 1)) :
    parity x = !decide ((0 : Int) ∈ S) := by
  have := Decodes_parity _ _ _ h
  rw [parity_cons, Bool.true_xor] at this
  have e : decide ((0 : Int) ∈ xorInsert 1 S) = decide ((0 : Int) ∈ S) := by
    rw [decide_eq_decide]; exact xorInsert_mem_other_iff 1 S 0 (by decide)
  rw [e] at this
  rw [← this, Bool.not_not]

/-! ## The scan of the active block

A scan in state B or C (or the skipped-cell scan after rule 5) crosses the
active block and lands on what follows it: the closing 1, the first cell of
the next block, or the 0 of a star. `landing` is the configuration reached,
`afterScan` the abstract configuration it stands for. -/

/-- The configuration after a scan that left the block `z` behind, exiting
    with parity `e` (state C when `e`), with `L` the cells left of the block
    and `rs` the items right of it. -/
def landing (L : List (Fin 3)) (rs : List Item) (rc : Closing) (z : Bits) (e : Bool) : LConfig :=
  match rs with
  | [] =>
      match rc with
      | Closing.one => ⟨(ofBits z).reverse ++ L, 1, [], stB e⟩
      | Closing.zero Rc =>
          if e then ⟨0 :: ((ofBits z).reverse.tail ++ L), 0, Rc, A⟩
          else ⟨(ofBits z).reverse ++ L, 0, Rc, B⟩
  | Item.set y _ :: rs' =>
      ⟨(ofBits z).reverse ++ L, toCell (y.headD false), (ofBits y).tail ++ renderR false rs' ++ rc.render, stB e⟩
  | Item.star :: rs' =>
      if e then ⟨0 :: ((ofBits z).reverse.tail ++ L), 0, renderR true rs' ++ rc.render, A⟩
      else ⟨(ofBits z).reverse ++ L, 0, renderR true rs' ++ rc.render, B⟩

/-- A scan from the cell `a` over the block `x` lands as `landing` says. -/
theorem scanRun (L : List (Fin 3)) (s a : Bool) (x : Bits) (rs : List Item) (rc : Closing)
    (hrs : ∀ y U, Item.set y U ∈ rs → y ≠ []) :
    lnSteps sys3 ⟨L, toCell a, ofBits x ++ renderR false rs ++ rc.render, stB s⟩ (x.length + 1)
      = some (landing L rs rc (scanFrom s (a :: x)) (s ^^ parity (a :: x))) := by
  cases rs with
  | nil =>
    cases rc with
    | one =>
      have := scanBlock L s a x 1 (by decide) []
      simpa [landing, Closing.render] using this
    | zero Rc =>
      by_cases he : (s ^^ parity (a :: x)) = true
      · have := scanBlock0C L s a x Rc he
        rw [he]
        simpa [landing, Closing.render, List.tail_reverse] using this
      · rw [Bool.not_eq_true] at he
        have := scanBlock0B L s a x Rc he
        rw [he]
        simpa [landing, Closing.render] using this
  | cons it rs' =>
    cases it with
    | set y U =>
      obtain ⟨y0, y', rfl⟩ := List.exists_cons_of_ne_nil (hrs y U List.mem_cons_self)
      have := scanBlock L s a x (toCell y0) (toCell_ne_zero y0) (ofBits y' ++ renderR false rs' ++ rc.render)
      simpa [landing] using this
    | star =>
      by_cases he : (s ^^ parity (a :: x)) = true
      · have := scanBlock0C L s a x (renderR true rs' ++ rc.render) he
        rw [he]
        simpa [landing, List.tail_reverse] using this
      · rw [Bool.not_eq_true] at he
        have := scanBlock0B L s a x (renderR true rs' ++ rc.render) he
        rw [he]
        simpa [landing] using this

/-- Moving one cell from the left context into the block. -/
theorem landing_cons (L : List (Fin 3)) (rs : List Item) (rc : Closing) (b : Bool) (z : Bits)
    (hz : z ≠ []) (e : Bool) : landing (toCell b :: L) rs rc z e = landing L rs rc (b :: z) e := by
  have hne : (ofBits z).reverse ≠ [] := by simpa [ofBits] using hz
  cases rs with
  | nil =>
    cases rc with
    | one => simp [landing]
    | zero Rc =>
      cases e with
      | false => simp [landing]
      | true => simp [landing, List.tail_append_of_ne_nil hne]
  | cons it rs' =>
    cases it with
    | set y U => simp [landing]
    | star =>
      cases e with
      | false => simp [landing]
      | true => simp [landing, List.tail_append_of_ne_nil hne]

/-- The abstract configuration after a scan: the block `z` with its set
    `S'` joins the left items, and the head is on the next item. -/
def afterScan (ls rs : List Item) (le : LeftEnd) (rc : Closing) (z : Bits) (S' : List Int)
    (st' : System4State) : AC :=
  ⟨Item.set z S' :: ls, rs.tail, le, rc, st',
   match rs with
   | [] => Focus.off
   | Item.set y U :: _ => Focus.setB (y.headD false) y.tail U
   | Item.star :: _ => Focus.star⟩

theorem st3_eq_stB (st : System4State) (h : st ≠ System4State.A) :
    st3 st = stB (decide (st = System4State.C)) := by
  cases st <;> simp_all [st3, stB]

theorem afterScan_toL (ls rs : List Item) (le : LeftEnd) (rc : Closing) (z : Bits) (S' : List Int)
    (st' : System4State) (hst' : st' ≠ System4State.A)
    (hrs : ∀ y U, Item.set y U ∈ rs → y ≠ []) :
    (afterScan ls rs le rc z S' st').toL
      = landing (renderL false ls ++ le.render) rs rc z (decide (st' = System4State.C)) := by
  cases rs with
  | nil =>
    cases rc with
    | one => simp [afterScan, AC.toL, landing, ofBits_reverse, st3_eq_stB st' hst']
    | zero Rc =>
      cases st' with
      | A => exact absurd rfl hst'
      | B => simp [afterScan, AC.toL, landing, ofBits_reverse]
      | C => simp [afterScan, AC.toL, landing, ofBits_reverse]
  | cons it rs' =>
    cases it with
    | set y U =>
      obtain ⟨y0, y', rfl⟩ := List.exists_cons_of_ne_nil (hrs y U List.mem_cons_self)
      simp [afterScan, AC.toL, landing, ofBits_reverse, st3_eq_stB st' hst']
    | star =>
      cases st' with
      | A => exact absurd rfl hst'
      | B => simp [afterScan, AC.toL, landing, ofBits_reverse]
      | C => simp [afterScan, AC.toL, landing, ofBits_reverse]

theorem afterScan_to4 (ls rs : List Item) (le : LeftEnd) (rc : Closing) (z : Bits) (S' : List Int)
    (st' : System4State) :
    (afterScan ls rs le rc z S' st').to4
      = ⟨ls.reverse.map Item.toElem ++ System4Elem.set S' :: rs.map Item.toElem,
         (ls.reverse.map Item.toElem).length + 1, st'⟩ := by
  cases rs with
  | nil => simp [afterScan, AC.to4, Item.toElem]
  | cons it rs' => cases it <;> simp [afterScan, AC.to4, Item.toElem]

theorem afterScan_OK (w h : Nat) (ls rs : List Item) (le : LeftEnd) (rc : Closing) (z : Bits)
    (S' : List Int) (st' : System4State) (hst' : st' ≠ System4State.A)
    (hN : h + 1 + 3 ≤ 2 ^ w) (hle : le.OK h (afterScan ls rs le rc z S' st').to4)
    (hls : ∀ it ∈ ls, ItemOK (2 ^ w) (h + 2) it) (hrs : ∀ it ∈ rs, ItemOK (2 ^ w) (h + 2) it)
    (hL : LeftOK le.isJunk ls) (hR : RightOK rs)
    (hz : ItemOK (2 ^ w) (h + 1) (Item.set z S'))
    (hlast : z.getLast? = some (decide (st' = System4State.C))) :
    (afterScan ls rs le rc z S' st').OK w h := by
  refine ⟨by omega, hle, ?_, ?_, ?_, ?_, ?_⟩
  · intro it hit
    rcases List.mem_cons.mp hit with rfl | hit
    · exact hz
    · exact ItemOK_mono _ _ _ _ (hls it hit) (by omega)
  · intro it hit
    exact ItemOK_mono _ _ _ _ (hrs it (List.mem_of_mem_tail hit)) (by omega)
  · show LeftOK le.isJunk (Item.set z S' :: ls)
    exact (LeftOK_set _ z S' ls).mpr hL
  · cases rs with
    | nil => trivial
    | cons it rs' =>
      cases it with
      | set y U => exact (RightOK_set y U rs').mp hR
      | star => exact (RightOK_star rs' hR).2
  · cases rs with
    | nil => trivial
    | cons it rs' =>
      cases it with
      | set y U =>
        have hy := hrs (Item.set y U) List.mem_cons_self
        obtain ⟨y0, y', rfl⟩ : ∃ y0 y', y = y0 :: y' := by
          cases y with
          | nil => simp [ItemOK] at hy; have := Nat.one_le_two_pow (n := w); omega
          | cons y0 y' => exact ⟨y0, y', rfl⟩
        exact ⟨hst', ItemOK_mono _ _ _ _ hy (by omega)⟩
      | star =>
        have hfirst := (RightOK_star rs' hR).1
        cases st' with
        | A => exact absurd rfl hst'
        | B => exact ⟨trivial, hfirst⟩
        | C =>
          refine ⟨Or.inl ?_, hfirst⟩
          show lastTrue z
          simpa [lastTrue] using hlast

/-! ## The per-rule lemmas -/

/-- The conclusion of every per-rule lemma: a run of System 3 from `c3` of
    at least one step reaches the System 3 side of an abstract configuration
    whose System 4 side is `c4'`. -/
def Matches (w h : Nat) (rc : Closing) (c3 : LConfig) (c4' : System4Config) : Prop :=
  ∃ k, 1 ≤ k ∧ ∃ a' : AC, a'.rc = rc ∧ lnSteps sys3 c3 k = some a'.toL ∧ c4' = a'.to4 ∧ a'.OK w h

theorem items_ne_nil (w k : Nat) (rs : List Item) (hrs : ∀ it ∈ rs, ItemOK (2 ^ w) k it) :
    ∀ y U, Item.set y U ∈ rs → y ≠ [] := by
  intro y U hy hnil
  have := (hrs _ hy).1
  rw [hnil] at this
  have := Nat.one_le_two_pow (n := w)
  simp at *
  omega

theorem item_len (w k : Nat) (y : Bits) (U : List Int) (h : ItemOK (2 ^ w) k (Item.set y U)) :
    y.length = 2 ^ w := h.1

theorem decide_ifCB (S : List Int) :
    decide ((if (0 : Int) ∈ S then System4State.C else System4State.B) = System4State.C)
      = decide ((0 : Int) ∈ S) := by
  by_cases h0 : (0 : Int) ∈ S <;> simp [h0]

theorem decide_ifBC (S : List Int) :
    decide ((if (0 : Int) ∈ S then System4State.B else System4State.C) = System4State.C)
      = !decide ((0 : Int) ∈ S) := by
  by_cases h0 : (0 : Int) ∈ S <;> simp [h0]

theorem ifCB_ne_A (S : List Int) :
    (if (0 : Int) ∈ S then System4State.C else System4State.B) ≠ System4State.A := by
  by_cases h0 : (0 : Int) ∈ S <;> simp [h0]

theorem ifBC_ne_A (S : List Int) :
    (if (0 : Int) ∈ S then System4State.B else System4State.C) ≠ System4State.A := by
  by_cases h0 : (0 : Int) ∈ S <;> simp [h0]

/-- Rule 3 in state B: a scan of the block from state B. -/
theorem case_scanB (w h : Nat) (ls rs : List Item) (le : LeftEnd) (rc : Closing) (x0 : Bool) (x' : Bits)
    (S : List Int) (c4' : System4Config)
    (hN : h + 1 + 3 ≤ 2 ^ w)
    (hls : ∀ it ∈ ls, ItemOK (2 ^ w) (h + 2) it) (hrs : ∀ it ∈ rs, ItemOK (2 ^ w) (h + 2) it)
    (hL : LeftOK le.isJunk ls) (hR : RightOK rs) (hit : ItemOK (2 ^ w) (h + 2) (Item.set (x0 :: x') S))
    (hle : le.OK (h + 1) (AC.mk ls rs le rc System4State.B (Focus.setB x0 x' S)).to4)
    (hs : System4.step (AC.mk ls rs le rc System4State.B (Focus.setB x0 x' S)).to4 = some c4') :
    Matches w h rc (AC.mk ls rs le rc System4State.B (Focus.setB x0 x' S)).toL c4' := by
  obtain ⟨hlen, hnd, hdec⟩ := hit
  have hle' := LeftEnd.OK_step le h _ c4' hs hle
  simp only [AC.to4] at hs
  rw [step_setB] at hs
  obtain rfl := Option.some.inj hs
  have hrs' := items_ne_nil w (h + 2) rs hrs
  have hpar := Decodes_parity _ _ _ hdec
  refine ⟨x'.length + 1, by omega,
    afterScan ls rs le rc (T (x0 :: x')) (decr S) (if (0 : Int) ∈ S then System4State.C else System4State.B),
    rfl, ?_, ?_, ?_⟩
  · rw [afterScan_toL _ _ _ _ _ _ _ (ifCB_ne_A S) hrs', decide_ifCB]
    show lnSteps sys3 ⟨renderL false ls ++ le.render, toCell x0,
      ofBits x' ++ renderR false rs ++ rc.render, stB false⟩ _ = _
    rw [scanRun _ _ _ _ _ _ hrs', Bool.false_xor, hpar]
    rfl
  · rw [afterScan_to4]; rfl
  · refine afterScan_OK w h ls rs le rc _ _ _ (ifCB_ne_A S) hN (by rw [afterScan_to4]; exact hle')
      hls hrs hL hR ⟨by simpa using hlen, decr_nodup S hnd, Decodes_T _ _ hnd _ hdec⟩ ?_
    rw [T_getLast? _ (by simp), hpar, decide_ifCB]

/-- Rule 3 in state C: a scan of the block from state C. -/
theorem case_scanC (w h : Nat) (ls rs : List Item) (le : LeftEnd) (rc : Closing) (x0 : Bool) (x' : Bits)
    (S : List Int) (c4' : System4Config)
    (hN : h + 1 + 3 ≤ 2 ^ w)
    (hls : ∀ it ∈ ls, ItemOK (2 ^ w) (h + 2) it) (hrs : ∀ it ∈ rs, ItemOK (2 ^ w) (h + 2) it)
    (hL : LeftOK le.isJunk ls) (hR : RightOK rs) (hit : ItemOK (2 ^ w) (h + 2) (Item.set (x0 :: x') S))
    (hle : le.OK (h + 1) (AC.mk ls rs le rc System4State.C (Focus.setB x0 x' S)).to4)
    (hs : System4.step (AC.mk ls rs le rc System4State.C (Focus.setB x0 x' S)).to4 = some c4') :
    Matches w h rc (AC.mk ls rs le rc System4State.C (Focus.setB x0 x' S)).toL c4' := by
  obtain ⟨hlen, hnd, hdec⟩ := hit
  have hle' := LeftEnd.OK_step le h _ c4' hs hle
  simp only [AC.to4] at hs
  rw [step_setC] at hs
  obtain rfl := Option.some.inj hs
  have hrs' := items_ne_nil w (h + 2) rs hrs
  have hpar := Decodes_parity _ _ _ hdec
  refine ⟨x'.length + 1, by omega,
    afterScan ls rs le rc (scanFrom true (x0 :: x')) (decr S)
      (if (0 : Int) ∈ S then System4State.B else System4State.C),
    rfl, ?_, ?_, ?_⟩
  · rw [afterScan_toL _ _ _ _ _ _ _ (ifBC_ne_A S) hrs', decide_ifBC]
    show lnSteps sys3 ⟨renderL false ls ++ le.render, toCell x0,
      ofBits x' ++ renderR false rs ++ rc.render, stB true⟩ _ = _
    rw [scanRun _ _ _ _ _ _ hrs', Bool.true_xor, hpar]
  · rw [afterScan_to4]; rfl
  · refine afterScan_OK w h ls rs le rc _ _ _ (ifBC_ne_A S) hN (by rw [afterScan_to4]; exact hle')
      hls hrs hL hR ⟨by simpa using hlen, decr_nodup S hnd,
        Decodes_scanC w x0 x' hlen S hnd (h + 1) (by omega) hdec⟩ ?_
    rw [scanFrom_getLast? _ _ (by simp), hpar, decide_ifBC, Bool.true_xor]

/-- Rule 3 in state C right after rule 5: the skipped-cell scan. -/
theorem case_scanT (w h : Nat) (ls rs : List Item) (le : LeftEnd) (rc : Closing) (x1 : Bool) (x' : Bits)
    (S : List Int) (c4' : System4Config)
    (hN : h + 1 + 3 ≤ 2 ^ w)
    (hls : ∀ it ∈ ls, ItemOK (2 ^ w) (h + 2) it) (hrs : ∀ it ∈ rs, ItemOK (2 ^ w) (h + 2) it)
    (hL : LeftOK le.isJunk ls) (hR : RightOK rs) (hnd : S.Nodup) (hlen : (true :: x1 :: x').length = 2 ^ w)
    (hdec : Decodes (true :: x1 :: x') (xorInsert 1 S) (h + 2))
    (hle : le.OK (h + 1) (AC.mk ls rs le rc System4State.C (Focus.setT x1 x' S)).to4)
    (hs : System4.step (AC.mk ls rs le rc System4State.C (Focus.setT x1 x' S)).to4 = some c4') :
    Matches w h rc (AC.mk ls rs le rc System4State.C (Focus.setT x1 x' S)).toL c4' := by
  have hle' := LeftEnd.OK_step le h _ c4' hs hle
  simp only [AC.to4] at hs
  rw [step_setC] at hs
  obtain rfl := Option.some.inj hs
  have hrs' := items_ne_nil w (h + 2) rs hrs
  have hpar := Decodes_transient_parity _ _ _ hdec
  refine ⟨x'.length + 1, by omega,
    afterScan ls rs le rc (true :: scanFrom false (x1 :: x')) (decr S)
      (if (0 : Int) ∈ S then System4State.B else System4State.C),
    rfl, ?_, ?_, ?_⟩
  · rw [afterScan_toL _ _ _ _ _ _ _ (ifBC_ne_A S) hrs', decide_ifBC,
      ← landing_cons _ _ _ true _ (by simp [scanFrom])]
    show lnSteps sys3 ⟨toCell true :: (renderL false ls ++ le.render), toCell x1,
      ofBits x' ++ renderR false rs ++ rc.render, stB false⟩ _ = _
    rw [scanRun _ _ _ _ _ _ hrs', Bool.false_xor, hpar]
  · rw [afterScan_to4]; rfl
  · refine afterScan_OK w h ls rs le rc _ _ _ (ifBC_ne_A S) hN (by rw [afterScan_to4]; exact hle')
      hls hrs hL hR ⟨by simpa using hlen, decr_nodup S hnd,
        Decodes_transient w (x1 :: x') hlen S hnd (h + 1) (by omega) hdec⟩ ?_
    rw [decide_ifBC, ← hpar]
    simp only [scanFrom, List.getLast?_cons_cons]
    rw [← scanFrom, scanFrom_getLast? _ _ (by simp), Bool.false_xor]

/-! ## Rule 1: the walk to the left -/

theorem ofBits_zipper (xl : Bits) (b : Bool) (xr : Bits) (R0 : List (Fin 3)) :
    (ofBits xl).reverse ++ toCell b :: (ofBits xr ++ R0) = ofBits (xl.reverse ++ b :: xr) ++ R0 := by
  rw [ofBits_append, ofBits_reverse, ofBits_cons, List.append_assoc, List.cons_append]

theorem leftEndRev_succ (m t : Nat) :
    leftEndRev m (t + 1) = List.replicate t 1 ++ 1 :: 2 :: 2 :: List.replicate m 0 := by
  simp only [leftEndRev, List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append]

/-- The turn at the left end: the walk over the block and the left end,
    the 0 turned into a 2, and the scan back over `2 2 1^t`, which becomes
    `2 1 1^t`, onto the first cell of the block. -/
theorem turnRun (xl : Bits) (b : Bool) (xr : Bits) (m' t : Nat) (R0 : List (Fin 3)) (x0 : Bool)
    (x' : Bits) (hx : xl.reverse ++ b :: xr = x0 :: x') :
    lnSteps sys3 ⟨ofBits xl ++ leftEndRev (m' + 1) t, toCell b, ofBits xr ++ R0, A⟩
        (xl.length + 2 * t + 6)
      = some ⟨leftEndRev m' (t + 1), toCell x0, ofBits x' ++ R0, B⟩ := by
  have hP : ∀ c ∈ ofBits xl ++ List.replicate t 1 ++ [2, 2], c ≠ 0 := by
    intro c hc
    simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil] at hc
    rcases hc with (hc | hc) | hc
    · exact ofBits_ne_zero xl c hc
    · rw [hc.2]; decide
    · rcases hc with rfl | rfl | h
      · decide
      · decide
      · exact absurd h (by simp)
  have hk : xl.length + 2 * t + 6
      = ((ofBits xl ++ List.replicate t 1 ++ [2, 2]).length + 1) + 1
          + ((true :: List.replicate t false).length + 1) := by
    simp; omega
  have e1 : (⟨ofBits xl ++ leftEndRev (m' + 1) t, toCell b, ofBits xr ++ R0, A⟩ : LConfig)
      = ⟨(ofBits xl ++ List.replicate t 1 ++ [2, 2]) ++ 0 :: List.replicate m' 0, toCell b,
         ofBits xr ++ R0, A⟩ := by
    simp [leftEndRev, List.replicate_succ]
  rw [hk, lnSteps_add, lnSteps_add, e1,
    walkLeft _ hP 0 (List.replicate m' 0) (toCell b) (toCell_ne_zero b) _, Option.bind_some]
  have e2 : (ofBits xl ++ List.replicate t 1 ++ [2, 2]).reverse ++ toCell b :: (ofBits xr ++ R0)
      = 2 :: (2 :: (List.replicate t 1 ++ toCell x0 :: (ofBits x' ++ R0))) := by
    rw [List.reverse_append, List.reverse_append, List.reverse_replicate, List.append_assoc,
      List.append_assoc, ofBits_zipper, hx, ofBits_cons, List.cons_append]
    rfl
  rw [e2, lnSteps_one, turnA, Option.bind_some]
  have e3 : (⟨2 :: List.replicate m' 0, 2, 2 :: (List.replicate t 1 ++ toCell x0 :: (ofBits x' ++ R0)), B⟩
      : LConfig)
      = ⟨2 :: List.replicate m' 0, toCell true,
         ofBits (true :: List.replicate t false) ++ toCell x0 :: (ofBits x' ++ R0), stB false⟩ := by
    simp [ofBits_replicate_false]
  rw [e3, scanBlock _ _ _ _ _ (toCell_ne_zero x0)]
  have e4 : scanFrom false (true :: true :: List.replicate t false)
      = true :: false :: List.replicate t false := by
    simp only [scanFrom, Bool.false_xor, Bool.true_xor, Bool.not_true]
    exact congrArg _ (congrArg _ (scanFrom_zeros false t))
  have e5 : parity (true :: true :: List.replicate t false) = false := by
    rw [parity_cons, parity_cons, show List.replicate t false = zeros t from rfl, parity_zeros]; rfl
  rw [e4, e5, leftEndRev_succ]
  simp [ofBits_replicate_false]

theorem ItemOK_reverse_split (N k : Nat) (y : Bits) (T : List Int) (b : Bool) (yl : Bits)
    (hy : y.reverse = b :: yl) (h : ItemOK N k (Item.set y T)) :
    ItemOK N k (Item.set (yl.reverse ++ b :: []) T) := by
  have : yl.reverse ++ b :: [] = y := by
    rw [← List.reverse_cons, ← hy, List.reverse_reverse]
  rw [this]; exact h

/-- Rule 1: a set in state A. -/
theorem case_setA (w h : Nat) (ls rs : List Item) (le : LeftEnd) (rc : Closing) (xl : Bits) (b : Bool) (xr : Bits)
    (S : List Int) (c4' : System4Config)
    (hN : h + 1 + 3 ≤ 2 ^ w)
    (hls : ∀ it ∈ ls, ItemOK (2 ^ w) (h + 2) it) (hrs : ∀ it ∈ rs, ItemOK (2 ^ w) (h + 2) it)
    (hL : LeftOK le.isJunk ls) (hR : RightOK rs) (hit : ItemOK (2 ^ w) (h + 2) (Item.set (xl.reverse ++ b :: xr) S))
    (hle : le.OK (h + 1) (AC.mk ls rs le rc System4State.A (Focus.setA xl b xr S)).to4)
    (hs : System4.step (AC.mk ls rs le rc System4State.A (Focus.setA xl b xr S)).to4 = some c4') :
    Matches w h rc (AC.mk ls rs le rc System4State.A (Focus.setA xl b xr S)).toL c4' := by
  have hle' := LeftEnd.OK_step le h _ c4' hs hle
  simp only [AC.to4] at hs hle
  have hrs2 : ∀ it ∈ Item.set (xl.reverse ++ b :: xr) S :: rs, ItemOK (2 ^ w) (h + 1) it := by
    intro it hit'
    rcases List.mem_cons.mp hit' with rfl | hit'
    · exact ItemOK_mono _ _ _ _ hit (by omega)
    · exact ItemOK_mono _ _ _ _ (hrs it hit') (by omega)
  have hR2 : RightOK (Item.set (xl.reverse ++ b :: xr) S :: rs) := (RightOK_set _ _ rs).mpr hR
  cases ls with
  | nil =>
    simp only [List.reverse_nil, List.map_nil, List.nil_append, List.length_nil] at hs
    rw [step_setA_zero] at hs
    obtain rfl := Option.some.inj hs
    cases le with
    | junk L =>
      exfalso
      have hS : SafeC (h + 1) ⟨System4Elem.set S :: List.map Item.toElem rs, 0, System4State.A⟩ := hle
      rcases SafeC_now _ _ hS with h0 | h0
      · exact h0 rfl
      · cases h0
    | zeros m t =>
      obtain ⟨hm, ht⟩ : h + 1 ≤ m ∧ 1 ≤ t := hle
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨x0, x', hx⟩ := List.exists_cons_of_ne_nil (l := xl.reverse ++ b :: xr) (by simp)
      refine ⟨xl.length + 2 * t + 6, by omega,
        AC.mk [] rs (LeftEnd.zeros m' (t + 1)) rc System4State.B (Focus.setB x0 x' S), rfl, ?_, ?_, ?_⟩
      · simp only [AC.toL, LeftEnd.render, renderL_nil, List.append_nil, List.nil_append,
          List.append_assoc, st3]
        exact turnRun xl b xr m' t _ x0 x' hx
      · simp [AC.to4]
      · dsimp only [AC.OK]
        refine ⟨by omega, ⟨by omega, by omega⟩, by simp, ?_, trivial, hR, by decide, ?_⟩
        · intro it hit'; exact ItemOK_mono _ _ _ _ (hrs it hit') (by omega)
        · rw [← hx]; exact ItemOK_mono _ _ _ _ hit (by omega)
  | cons it ls' =>
    have hLne : (it :: ls').reverse.map Item.toElem ≠ [] := by simp
    rw [step_setA _ _ _ hLne] at hs
    obtain rfl := Option.some.inj hs
    have hls' : ∀ it' ∈ ls', ItemOK (2 ^ w) (h + 1) it' := fun it' hit' =>
      ItemOK_mono _ _ _ _ (hls it' (List.mem_cons_of_mem _ hit')) (by omega)
    cases it with
    | set y T =>
      have hy0 := hls (Item.set y T) List.mem_cons_self
      obtain ⟨b', yl, hy⟩ := List.exists_cons_of_ne_nil (l := y.reverse)
        (by intro hnil; have h1 := item_len w _ y T hy0; rw [← List.length_reverse, hnil] at h1
            have h2 := Nat.one_le_two_pow (n := w); simp at h1; omega)
      refine ⟨xl.length + 1, by omega,
        AC.mk ls' (Item.set (xl.reverse ++ b :: xr) S :: rs) le rc System4State.A (Focus.setA yl b' [] T),
        rfl, ?_, ?_, ?_⟩
      · have hrun := walkLeft (ofBits xl) (ofBits_ne_zero xl) (toCell b')
          (ofBits yl ++ renderL false ls' ++ le.render) (toCell b) (toCell_ne_zero b)
          (ofBits xr ++ renderR false rs ++ rc.render)
        rw [length_ofBits] at hrun
        simp only [AC.toL, renderL_set_false, renderR_set_false, hy, ofBits_cons, ofBits_nil,
          List.nil_append, List.append_assoc, List.cons_append] at hrun ⊢
        rw [hrun, ofBits_zipper]
      · simp [AC.to4, Item.toElem]
      · dsimp only [AC.OK]
        refine ⟨by omega, ?_, hls', hrs2, (LeftOK_set _ y T ls').mp hL, hR2, rfl, ?_⟩
        · simp only [AC.to4]
          simpa [Item.toElem] using hle'
        · exact ItemOK_reverse_split _ _ y T b' yl hy (ItemOK_mono _ _ _ _ hy0 (by omega))
    | star =>
      rcases LeftOK_star _ ls' hL with ⟨hlast, hL'⟩ | ⟨rfl, hj⟩
      · refine ⟨xl.length + 1, by omega,
          AC.mk ls' (Item.set (xl.reverse ++ b :: xr) S :: rs) le rc System4State.A Focus.star,
          rfl, ?_, ?_, ?_⟩
        · have hrun := walkLeft (ofBits xl) (ofBits_ne_zero xl) 0
            (renderL true ls' ++ le.render) (toCell b) (toCell_ne_zero b)
            (ofBits xr ++ renderR false rs ++ rc.render)
          rw [length_ofBits] at hrun
          simp only [AC.toL, renderL_star, renderR_set_false, List.append_assoc, List.cons_append] at hrun ⊢
          rw [hrun, ofBits_zipper]
        · simp [AC.to4, Item.toElem]
        · dsimp only [AC.OK]
          refine ⟨by omega, ?_, hls', hrs2, hL', hR2, hlast, trivial⟩
          simp only [AC.to4]
          simpa [Item.toElem] using hle'
      · exfalso
        cases le with
        | zeros m t => cases hj
        | junk L =>
          have hS : SafeC h ⟨[System4Elem.star] ++ System4Elem.set S :: List.map Item.toElem rs,
              [System4Elem.star].length - 1, System4State.A⟩ := by
            have := hle'
            simp only [Item.toElem, List.map_cons, List.map_nil, List.singleton_append,
              List.length_singleton, Nat.sub_self] at this ⊢
            exact this
          rcases SafeC_now _ _ hS with h0 | h0
          · exact h0 rfl
          · cases h0

/-! ## Rules 2, 4, 5: one step at a star -/

/-- Rule 2: a star in state A. -/
theorem case_starA (w h : Nat) (ls rs : List Item) (le : LeftEnd) (rc : Closing) (c4' : System4Config)
    (hN : h + 1 + 3 ≤ 2 ^ w)
    (hls : ∀ it ∈ ls, ItemOK (2 ^ w) (h + 2) it) (hrs : ∀ it ∈ rs, ItemOK (2 ^ w) (h + 2) it)
    (hL : LeftOK le.isJunk ls) (hR : RightOK rs) (hlast : HeadLastTrue ls) (hset : HeadSet rs)
    (hle : le.OK (h + 1) (AC.mk ls rs le rc System4State.A Focus.star).to4)
    (hs : System4.step (AC.mk ls rs le rc System4State.A Focus.star).to4 = some c4') :
    Matches w h rc (AC.mk ls rs le rc System4State.A Focus.star).toL c4' := by
  have hle' := LeftEnd.OK_step le h _ c4' hs hle
  match rs, hset with
  | Item.set y U :: rs', _ =>
    simp only [AC.to4] at hs
    rw [List.map_cons, step_starA] at hs
    obtain rfl := Option.some.inj hs
    have hy0 := hrs (Item.set y U) List.mem_cons_self
    obtain ⟨y0, y', rfl⟩ := List.exists_cons_of_ne_nil (items_ne_nil w _ _ hrs y U List.mem_cons_self)
    refine ⟨1, le_refl 1, AC.mk ls rs' le rc System4State.B (Focus.setB y0 y' U), rfl, ?_, ?_, ?_⟩
    · simp only [AC.toL, renderR_set_false, ofBits_cons, List.append_assoc, List.cons_append]
      rw [lnSteps_one, turnA, ← List.cons_append, renderL_of_headLastTrue ls hlast]
      rfl
    · simp [AC.to4, Item.toElem]
    · dsimp only [AC.OK]
      refine ⟨by omega, by simpa [AC.to4, Item.toElem] using hle', ?_, ?_, hL,
        (RightOK_set _ U rs').mp hR, ?_⟩
      · intro it hit; exact ItemOK_mono _ _ _ _ (hls it hit) (by omega)
      · intro it hit; exact ItemOK_mono _ _ _ _ (hrs it (List.mem_cons_of_mem _ hit)) (by omega)
      · exact ⟨by decide, ItemOK_mono _ _ _ _ hy0 (by omega)⟩

/-- Rule 4: a star in state B. -/
theorem case_starB (w h : Nat) (ls rs : List Item) (le : LeftEnd) (rc : Closing) (c4' : System4Config)
    (hN : h + 1 + 3 ≤ 2 ^ w)
    (hls : ∀ it ∈ ls, ItemOK (2 ^ w) (h + 2) it) (hrs : ∀ it ∈ rs, ItemOK (2 ^ w) (h + 2) it)
    (hL : LeftOK le.isJunk ls) (hR : RightOK rs) (hset : HeadSet ls) (hfirst : HeadFirstTrue rs)
    (hle : le.OK (h + 1) (AC.mk ls rs le rc System4State.B Focus.star).to4)
    (hs : System4.step (AC.mk ls rs le rc System4State.B Focus.star).to4 = some c4') :
    Matches w h rc (AC.mk ls rs le rc System4State.B Focus.star).toL c4' := by
  have hle' := LeftEnd.OK_step le h _ c4' hs hle
  match ls, hset with
  | Item.set y T :: ls', _ =>
    simp only [AC.to4] at hs
    have hLne : (Item.set y T :: ls').reverse.map Item.toElem ≠ [] := by simp
    rw [step_starB _ _ hLne] at hs
    obtain rfl := Option.some.inj hs
    have hy0 := hls (Item.set y T) List.mem_cons_self
    obtain ⟨b', yl, hy⟩ := List.exists_cons_of_ne_nil (l := y.reverse)
      (by intro hnil; have h1 := item_len w _ y T hy0; rw [← List.length_reverse, hnil] at h1
          have h2 := Nat.one_le_two_pow (n := w); simp at h1; omega)
    refine ⟨1, le_refl 1, AC.mk ls' rs le rc System4State.A (Focus.setA yl b' [] T), rfl, ?_, ?_, ?_⟩
    · simp only [AC.toL, renderL_set_false, hy, ofBits_cons, ofBits_nil, List.nil_append,
        List.append_assoc, List.cons_append]
      rw [lnSteps_one, starB, ← List.cons_append, renderR_of_headFirstTrue rs hfirst]
    · simp [AC.to4, Item.toElem]
    · dsimp only [AC.OK]
      refine ⟨by omega, by simpa [AC.to4, Item.toElem] using hle', ?_, ?_,
        (LeftOK_set _ y T ls').mp hL, hR, rfl, ?_⟩
      · intro it hit; exact ItemOK_mono _ _ _ _ (hls it (List.mem_cons_of_mem _ hit)) (by omega)
      · intro it hit; exact ItemOK_mono _ _ _ _ (hrs it hit) (by omega)
      · exact ItemOK_reverse_split _ _ y T b' yl hy (ItemOK_mono _ _ _ _ hy0 (by omega))

/-- Rule 5: a star in state C. -/
theorem case_starC (w h : Nat) (ls rs : List Item) (le : LeftEnd) (rc : Closing) (c4' : System4Config)
    (hN : h + 1 + 3 ≤ 2 ^ w)
    (hls : ∀ it ∈ ls, ItemOK (2 ^ w) (h + 2) it) (hrs : ∀ it ∈ rs, ItemOK (2 ^ w) (h + 2) it)
    (hL : LeftOK le.isJunk ls) (hR : RightOK rs) (hlast : LeftLast le.isJunk ls)
    (hfirst : HeadFirstTrue rs)
    (hle : le.OK (h + 1) (AC.mk ls rs le rc System4State.C Focus.star).to4)
    (hs : System4.step (AC.mk ls rs le rc System4State.C Focus.star).to4 = some c4') :
    Matches w h rc (AC.mk ls rs le rc System4State.C Focus.star).toL c4' := by
  have hle' := LeftEnd.OK_step le h _ c4' hs hle
  match rs, hfirst with
  | Item.set y U :: rs', hfirst =>
    obtain ⟨y', rfl⟩ := firstTrue_cons y hfirst
    have hy0 := hrs (Item.set (true :: y') U) List.mem_cons_self
    obtain ⟨hlen, hUnd, hUdec⟩ := hy0
    obtain ⟨y1, y'', rfl⟩ := List.exists_cons_of_ne_nil (l := y')
      (by intro hnil; rw [hnil] at hlen; simp at hlen; omega)
    simp only [AC.to4, List.map_cons, Item.toElem] at hs
    rw [step_starC] at hs
    obtain rfl := Option.some.inj hs
    refine ⟨1, le_refl 1,
      AC.mk (Item.star :: ls) rs' le rc System4State.C (Focus.setT y1 y'' (xorInsert 1 U)), rfl,
      ?_, ?_, ?_⟩
    · simp only [AC.toL, renderR_set_true, renderL_star, ofBits_cons, List.tail_cons,
        List.append_assoc, List.cons_append]
      rw [lnSteps_one, turnA]
    · simp [AC.to4, Item.toElem]
    · dsimp only [AC.OK]
      refine ⟨by omega, by simpa [AC.to4, Item.toElem] using hle', ?_, ?_,
        LeftOK_of_leftLast _ ls hL hlast,
        (RightOK_set _ U rs').mp hR, rfl, xorInsert_nodup 1 U hUnd, hlen, ?_⟩
      · intro it hit
        rcases List.mem_cons.mp hit with rfl | hit
        · trivial
        · exact ItemOK_mono _ _ _ _ (hls it hit) (by omega)
      · intro it hit; exact ItemOK_mono _ _ _ _ (hrs it (List.mem_cons_of_mem _ hit)) (by omega)
      · exact Decodes_xorInsert_twice _ _ hUnd _ (Decodes_mono _ _ _ _ hUdec (by omega))

/-- Past the right end System 4 is stuck. -/
theorem step_off (L : List System4Elem) (st : System4State) :
    System4.step ⟨L, L.length, st⟩ = none := by
  unfold System4.step
  rw [dif_neg (lt_irrefl _)]

/-! ## The step lemma and the forward simulation -/

/-- Every System 4 step from an abstract configuration is matched by a run
    of System 3 to the abstract configuration of the result. -/
theorem ac_step (w h : Nat) (a : AC) (hOK : a.OK w (h + 1)) (c4' : System4Config)
    (hs : System4.step a.to4 = some c4') : Matches w h a.rc a.toL c4' := by
  obtain ⟨ls, rs, le, rc, st, foc⟩ := a
  obtain ⟨hN, hle, hls, hrs, hL, hR, hfoc⟩ := hOK
  cases foc with
  | setA xl b xr S =>
    obtain ⟨rfl, hit⟩ := hfoc
    exact case_setA w h ls rs le rc xl b xr S c4' hN hls hrs hL hR hit hle hs
  | setB x0 x' S =>
    obtain ⟨hst, hit⟩ := hfoc
    cases st with
    | A => exact absurd rfl hst
    | B => exact case_scanB w h ls rs le rc x0 x' S c4' hN hls hrs hL hR hit hle hs
    | C => exact case_scanC w h ls rs le rc x0 x' S c4' hN hls hrs hL hR hit hle hs
  | setT x1 x' S =>
    obtain ⟨rfl, hnd, hlen, hdec⟩ := hfoc
    exact case_scanT w h ls rs le rc x1 x' S c4' hN hls hrs hL hR hnd hlen hdec hle hs
  | star =>
    cases st with
    | A => exact case_starA w h ls rs le rc c4' hN hls hrs hL hR hfoc.1 hfoc.2 hle hs
    | B => exact case_starB w h ls rs le rc c4' hN hls hrs hL hR hfoc.1 hfoc.2 hle hs
    | C => exact case_starC w h ls rs le rc c4' hN hls hrs hL hR hfoc.1 hfoc.2 hle hs
  | off =>
    exfalso
    simp only [AC.to4] at hs
    rw [step_off] at hs
    cases hs

/-- Link D as a `ForwardSim`: System 3 tracks the fuelled System 4 through
    `Rep3`, the fuel being the budget of scans the blocks are good for. -/
theorem sys4_sys3_forwardSim (w : Nat) (rc : Closing) :
    ForwardSim (fueled system4Sys) (lsys sys3) (fun p c => Rep3 rc c p.1 w p.2) := by
  rintro ⟨c4, n⟩ c3 ⟨a, rfl, hOK, rfl, rfl⟩ p hstep
  cases n with
  | zero => rw [fueled_step_zero] at hstep; exact absurd hstep (by simp)
  | succ h =>
    rw [fueled_step_succ] at hstep
    cases hs : system4Sys.step a.to4 with
    | none => rw [hs] at hstep; exact absurd hstep (by simp)
    | some c4' =>
      rw [hs, Option.map_some] at hstep
      obtain rfl : p = (c4', h) := (Option.some.inj hstep).symm
      obtain ⟨k, hk, a', hrc, hrun, rfl, hOK'⟩ := ac_step w h a hOK c4' hs
      exact ⟨k, hk, a'.toL, hrun, a', hrc, hOK', rfl, rfl⟩

/-! ## The initial tape

The blocks of the initial tape are Smith's (`s42s0-3.pl`): the XOR of the
rows of the elements, of the last row (all 2s), and, when the first cell
would otherwise be a 1, of the row before it. The last two rows have their
parity at the scans `N - 1` and `N - 2` only, outside the window, and make
the first cell a 2, so that a star may stand in its place. -/

theorem row_head? (w i : Nat) : (row (2 ^ w) i).head? = some true := by
  induction i with
  | zero =>
    simp only [row, unit]
    rfl
  | succ i ih =>
    obtain ⟨x', hx⟩ : ∃ x', row (2 ^ w) i = true :: x' := by
      cases hr : row (2 ^ w) i with
      | nil => rw [hr] at ih; simp at ih
      | cons a x' => rw [hr] at ih; simp at ih; exact ⟨x', by rw [ih]⟩
    rw [row, stepR, hx, shiftR, List.dropLast_cons_of_ne_nil (by simp), xorB_cons]
    rfl

/-- The XOR of the rows of the elements and of the last row. -/
def baseSet (N : Nat) (S : List Int) : Bits :=
  S.foldr (fun e acc => xorB (row N e.toNat) acc) (ones N)

/-- Smith's block of a set: `baseSet`, with the row `N - 2` added when the
    first cell is a 1. -/
def encSet (N : Nat) (S : List Int) : Bits :=
  if (baseSet N S).head? = some true then baseSet N S else xorB (baseSet N S) (row N (N - 2))

theorem length_baseSet (w : Nat) (S : List Int) : (baseSet (2 ^ w) S).length = 2 ^ w := by
  induction S with
  | nil => simp [baseSet]
  | cons e S ih =>
    simp only [baseSet, List.foldr_cons] at ih ⊢
    rw [length_xorB _ _ (by rw [ih, length_row _ _ Nat.one_le_two_pow]), length_row _ _ Nat.one_le_two_pow]

theorem length_encSet (w : Nat) (S : List Int) : (encSet (2 ^ w) S).length = 2 ^ w := by
  unfold encSet
  split
  · exact length_baseSet w S
  · rw [length_xorB _ _ (by rw [length_baseSet, length_row _ _ Nat.one_le_two_pow]), length_baseSet]

theorem parAt_baseSet (w : Nat) (S : List Int) (hS : S.Nodup)
    (hb : ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w) (j : Nat) (hj : j < 2 ^ w - 1) :
    parAt (baseSet (2 ^ w) S) j = decide ((j : Int) ∈ S) := by
  induction S with
  | nil =>
    simp only [baseSet, List.foldr_nil, List.not_mem_nil, decide_false]
    rw [← row_last_ones, parAt_row w _ j (by have := Nat.one_le_two_pow (n := w); omega) (by omega)]
    simp; omega
  | cons e S ih =>
    have hnd := List.nodup_cons.mp hS
    have he := hb e List.mem_cons_self
    have hb' : ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w := fun e he => hb e (List.mem_cons_of_mem _ he)
    simp only [baseSet, List.foldr_cons] at ih ⊢
    rw [parAt_xor _ _ (by rw [length_row _ _ Nat.one_le_two_pow]; exact (length_baseSet w S).symm),
      ih hnd.2 hb', parAt_row w _ j (by omega) (by omega)]
    by_cases hje : (j : Int) = e
    · have h1 : decide (j = e.toNat) = true := decide_eq_true (by omega)
      have h2 : (j : Int) ∉ S := by rw [hje]; exact hnd.1
      rw [h1, decide_eq_false h2, decide_eq_true (List.mem_cons.mpr (Or.inl hje))]
      rfl
    · have h1 : decide (j = e.toNat) = false := decide_eq_false (by omega)
      rw [h1, Bool.false_xor, decide_eq_decide, List.mem_cons]
      exact ⟨Or.inr, fun h => h.resolve_left hje⟩

theorem parAt_encSet (w : Nat) (S : List Int) (hS : S.Nodup)
    (hb : ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w) (j : Nat) (hj : j < 2 ^ w - 2) :
    parAt (encSet (2 ^ w) S) j = decide ((j : Int) ∈ S) := by
  unfold encSet
  split
  · exact parAt_baseSet w S hS hb j (by omega)
  · rw [parAt_xor _ _ (by rw [length_baseSet, length_row _ _ Nat.one_le_two_pow]),
      parAt_baseSet w S hS hb j (by omega), parAt_row w _ j (by omega) (by omega)]
    have : j ≠ 2 ^ w - 2 := by omega
    simp [this]

theorem Decodes_encSet (w k : Nat) (S : List Int) (hS : S.Nodup)
    (hb : ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w) (hk : k + 2 ≤ 2 ^ w) : Decodes (encSet (2 ^ w) S) S k :=
  fun j hj => parAt_encSet w S hS hb j (by omega)

theorem firstTrue_encSet (w : Nat) (S : List Int) : firstTrue (encSet (2 ^ w) S) := by
  unfold firstTrue encSet
  split
  · assumption
  · rename_i hne
    obtain ⟨b, rest, hb⟩ := List.exists_cons_of_ne_nil (l := baseSet (2 ^ w) S)
      (by intro hnil; have h1 := length_baseSet w S; rw [hnil] at h1
          have h2 := Nat.one_le_two_pow (n := w); simp at h1; omega)
    obtain ⟨rest', hr⟩ : ∃ rest', row (2 ^ w) (2 ^ w - 2) = true :: rest' := by
      have := row_head? w (2 ^ w - 2)
      cases hrow : row (2 ^ w) (2 ^ w - 2) with
      | nil => rw [hrow] at this; simp at this
      | cons a r => rw [hrow] at this; simp at this; exact ⟨r, by rw [this]⟩
    rw [hb] at hne ⊢
    rw [hr, xorB_cons]
    cases b with
    | true => exact absurd rfl hne
    | false => rfl

theorem ItemOK_encSet (w k : Nat) (S : List Int) (hS : S.Nodup)
    (hb : ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w) (hk : k + 2 ≤ 2 ^ w) :
    ItemOK (2 ^ w) k (Item.set (encSet (2 ^ w) S) S) :=
  ⟨length_encSet w S, hS, Decodes_encSet w k S hS hb hk⟩

/-- The item of a System 4 element on the initial tape. -/
def toItem (N : Nat) : System4Elem → Item
  | System4Elem.set S => Item.set (encSet N S) S
  | System4Elem.star => Item.star

@[simp] theorem toElem_toItem (N : Nat) (e : System4Elem) : (toItem N e).toElem = e := by
  cases e <;> rfl

theorem RightOK_map (w : Nat) (l : List System4Elem) (hadj : noAdjacentStars l = true)
    (hlast : l.getLast? ≠ some System4Elem.star) : RightOK (l.map (toItem (2 ^ w))) := by
  induction l with
  | nil => trivial
  | cons e rest ih =>
    cases e with
    | set S =>
      rw [List.map_cons]
      show RightOK (Item.set _ S :: _)
      rw [RightOK_set]
      refine ih (noAdjacentStars_tail _ _ hadj) ?_
      cases rest with
      | nil => simp
      | cons e' rest' => simpa using hlast
    | star =>
      cases rest with
      | nil => exact absurd rfl hlast
      | cons e' rest' =>
        cases e' with
        | star =>
          have := noAdjacentStars_cons_head _ _ _ hadj (List.head?_cons ..)
          simp [System4Elem.isStar] at this
        | set S =>
          rw [List.map_cons, List.map_cons]
          show firstTrue _ ∧ RightOK (Item.set _ S :: _)
          refine ⟨firstTrue_encSet w S, ?_⟩
          rw [RightOK_set]
          exact ih (noAdjacentStars_tail _ _ (noAdjacentStars_tail _ _ hadj)) (by simpa using hlast)

/-- The abstract configuration of the initial tape for the System 4
    configuration `<set S0 :: rest, 0, A>`: no item left of the head, the
    left end `0^h 2 2 1`, the head on the first cell of the block of `S0`
    in state A. -/
def initAC (w h : Nat) (S0 : List Int) (rest : List System4Elem) : AC :=
  ⟨[], rest.map (toItem (2 ^ w)), LeftEnd.zeros h 1, Closing.one, System4State.A,
   Focus.setA [] ((encSet (2 ^ w) S0).headD false) (encSet (2 ^ w) S0).tail S0⟩

theorem encSet_cons (w : Nat) (S : List Int) :
    (encSet (2 ^ w) S).headD false :: (encSet (2 ^ w) S).tail = encSet (2 ^ w) S := by
  obtain ⟨b, rest, hb⟩ := List.exists_cons_of_ne_nil (l := encSet (2 ^ w) S)
    (by intro hnil; have h1 := length_encSet w S; rw [hnil] at h1
        have h2 := Nat.one_le_two_pow (n := w); simp at h1; omega)
  rw [hb]; rfl

theorem initAC_to4 (w h : Nat) (S0 : List Int) (rest : List System4Elem) :
    (initAC w h S0 rest).to4 = ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩ := by
  simp [initAC, AC.to4, List.map_map, Function.comp_def]

theorem initAC_OK (w h : Nat) (S0 : List Int) (rest : List System4Elem)
    (hN : h + 3 ≤ 2 ^ w)
    (hwf : System4Config.WellFormed ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩)
    (hlast : (System4Elem.set S0 :: rest).getLast? ≠ some System4Elem.star)
    (hb : ∀ S, System4Elem.set S ∈ System4Elem.set S0 :: rest → ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w) :
    (initAC w h S0 rest).OK w h := by
  obtain ⟨_, hadj, hnd⟩ := hwf
  have hnd' : ∀ S, System4Elem.set S ∈ System4Elem.set S0 :: rest → S.Nodup := by
    intro S hS
    have := (List.all_eq_true.mp hnd) _ hS
    simpa [System4Elem.setNodup] using this
  dsimp only [AC.OK, initAC]
  refine ⟨hN, ⟨le_refl h, le_refl 1⟩, by simp, ?_, trivial, ?_, rfl, ?_⟩
  · intro it hit
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hit
    cases e with
    | star => trivial
    | set S =>
      exact ItemOK_encSet w (h + 1) S (hnd' S (List.mem_cons_of_mem _ he))
        (hb S (List.mem_cons_of_mem _ he)) (by omega)
  · refine RightOK_map w rest (noAdjacentStars_tail _ _ hadj) ?_
    cases rest with
    | nil => simp
    | cons e' rest' => simpa using hlast
  · rw [List.reverse_nil, List.nil_append, encSet_cons]
    exact ItemOK_encSet w (h + 1) S0 (hnd' S0 List.mem_cons_self) (hb S0 List.mem_cons_self) (by omega)

/-- The initial condition of link D: the System 3 tape of `initAC` stands
    for the System 4 configuration. -/
theorem rep3_init (w h : Nat) (S0 : List Int) (rest : List System4Elem)
    (hN : h + 3 ≤ 2 ^ w)
    (hwf : System4Config.WellFormed ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩)
    (hlast : (System4Elem.set S0 :: rest).getLast? ≠ some System4Elem.star)
    (hb : ∀ S, System4Elem.set S ∈ System4Elem.set S0 :: rest → ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w) :
    Rep3 Closing.one (initAC w h S0 rest).toL ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩ w h :=
  ⟨initAC w h S0 rest, rfl, initAC_OK w h S0 rest hN hwf hlast hb, rfl, (initAC_to4 w h S0 rest).symm⟩

/-! ## T3: System 4 to System 0 -/

/-- Links D and E composed: System 0 tracks the fuelled System 4 through
    `Rep3` and the relabelings `phi2`, `phi3`. -/
theorem sys4_sys0_forwardSim (w : Nat) (rc : Closing) :
    ForwardSim (fueled system4Sys) (lsys sys0)
      (fun p c0 => ∃ c3, Rep3 rc c3 p.1 w p.2 ∧ c0 = phi2 (phi3 c3)) :=
  ForwardSim_congr (ForwardSim_comp (sys4_sys3_forwardSim w rc) sys3_sys0_forwardSim)
    (fun _ _ => Iff.rfl)

/-- T3 in finite form: a System 4 run of `n <= h` steps from a well-formed
    tape whose head is on its leftmost element in state A, with sets bounded
    by `2^w`, is tracked by the System 0 run from the relabeled initial tape
    at strictly increasing times, the tapes standing in `Rep3` with the
    budget counting down. -/
theorem conjecture3_finite (w h n : Nat) (S0 : List Int) (rest : List System4Elem)
    (hN : h + 3 ≤ 2 ^ w)
    (hwf : System4Config.WellFormed ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩)
    (hlast : (System4Elem.set S0 :: rest).getLast? ≠ some System4Elem.star)
    (hb : ∀ S, System4Elem.set S ∈ System4Elem.set S0 :: rest → ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w)
    (hn : n ≤ h) (c' : System4Config)
    (hrun : System4.nSteps ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩ n = some c') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ i, i < n → times i < times (i + 1)) ∧
      ∀ i, i ≤ n → ∃ ci c3i, System4.nSteps ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩ i = some ci ∧
        lnSteps sys0 (phi2 (phi3 (initAC w h S0 rest).toL)) (times i) = some (phi2 (phi3 c3i)) ∧
        Rep3 Closing.one c3i ci w (h - i) := by
  obtain ⟨times, h0, hmono, htr⟩ := ForwardSim_nSteps (sys4_sys0_forwardSim w Closing.one) n
    (⟨System4Elem.set S0 :: rest, 0, System4State.A⟩, h) (phi2 (phi3 (initAC w h S0 rest).toL))
    ⟨(initAC w h S0 rest).toL, rep3_init w h S0 rest hN hwf hlast hb, rfl⟩
    (c', h - n) (by rw [fueled_nSteps _ _ _ _ hn, system4Sys_nSteps, hrun]; rfl)
  refine ⟨times, h0, hmono, fun i hi => ?_⟩
  obtain ⟨⟨ci, hi'⟩, c0i, hsi, hci, c3i, hrep, rfl⟩ := htr i hi
  rw [fueled_nSteps _ _ _ _ (by omega), system4Sys_nSteps] at hsi
  cases hsi4 : System4.nSteps ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩ i with
  | none => rw [hsi4] at hsi; simp at hsi
  | some ci0 =>
    rw [hsi4, Option.map_some] at hsi
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsi)
    exact ⟨ci0, c3i, rfl, hci, hrep⟩

end Smith
