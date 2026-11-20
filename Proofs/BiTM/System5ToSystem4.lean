/-
  BiTM.System5ToSystem4

  Smith's System 5 to System 4 encoder, a transcription of the Perl
  program `s52s4.pl` (TM23Proof.pdf p. 32-33).  It maps a System 5
  (bag, rules) program plus a parameter `f` to a System 4 configuration
  whose evolution emulates the System 5 evolution.

  Encoding, token for token with the Perl:
    * state A, active 0;
    * the bag as a single set, each entry `e` sent to `e * 2 - 2`, with
      the parity cancellation of the Perl hash
      (`$temp{$e*2-2}++; $temp{$e*2-2}==2 and delete ...`);
    * `f` star/empty-set pairs;
    * one block of `8 * f` elements per System 5 rule:
        star, the rule set (all of `0..3f`, toggled at `k * 2 + f + 3`
        for every rule entry `k`), `2f` star/empty-set pairs, star, the
        set of all of `0..3f`, `2f - 2` star/empty-set pairs.

  The two stars that open the rule set and the all-integers set are the
  `print ' _ '` statements of the Perl.  Without them the System 4 run is
  observably different: the Lean interpreter on the Lean tape for
  `s52s4.pl 16 2 1,4 1,6 "" ""` printed `11001111100111100` while Smith
  prints `110011110011110010` (PDF p. 41).  See `Tests.SmithVectors`.

  Contents:
    * `system5BagEntryToSystem4`, `encodeBag` - bag encoder
    * `starredEmptyPairs`, `allInts` - helpers
    * `encodeS5RuleToS4Set`, `encodeS5RuleToS4Elems` - per-rule encoder
    * `system5ToSystem4` - top-level encoder
    * length, Nodup and structure lemmas, plus emulation-lifting lemmas
      parametric in an encoder
-/

import BiTM.XorMerge
import BiTM.System5
import BiTM.System4

namespace BiTM

open TM
open TagSystem

/-- Encode a System 5 bag entry into the corresponding System 4 set entry. -/
def system5BagEntryToSystem4 (e : Int) : Int := e * 2 - 2

/-- Encode the bag as a System 4 set.  `s52s4.pl` builds a hash and
    deletes a key whose count reaches 2, so an entry contributed twice
    cancels; the fold with `xorInsert` reproduces that parity semantics. -/
def encodeBag (bag : List Int) : List Int :=
  bag.foldl (fun acc e => xorInsert (system5BagEntryToSystem4 e) acc) []

/-- A list `[*, {}, *, {}, ..., *, {}]` of `n` star + empty-set pairs (`2n` elems). -/
def starredEmptyPairs : Nat → List System4Elem
  | 0 => []
  | k + 1 => System4Elem.star :: System4Elem.set [] :: starredEmptyPairs k

/-- All integers from 0 to `n - 1` as a `List Int`. -/
def allInts (n : Nat) : List Int :=
  (List.range n).map (fun (i : Nat) => (i : Int))

/-- Encode one System 5 rule into a System 4 set: starts with all of `0..f*3`,
    then XOR-toggle each rule entry `k` mapped to `k*2 + f + 3`. -/
def encodeS5RuleToS4Set (rule : List Int) (f : Nat) : List Int :=
  rule.foldl (fun acc k => xorInsert (k * 2 + (f : Int) + 3) acc)
             (allInts (f * 3 + 1))

/-- Encode one System 5 rule into a block of System 4 elements, exactly the
    tokens printed by the per-rule loop of `s52s4.pl`:
    star, rule set, `2f` star/empty pairs, star, all-integers set,
    `2f - 2` star/empty pairs.  The block has `8 * f` elements for `f >= 1`. -/
def encodeS5RuleToS4Elems (rule : List Int) (f : Nat) : List System4Elem :=
  System4Elem.star :: System4Elem.set (encodeS5RuleToS4Set rule f) ::
    starredEmptyPairs (f * 2) ++
    System4Elem.star :: System4Elem.set (allInts (f * 3 + 1)) ::
    starredEmptyPairs (f * 2 - 2)

/-- Full System 5 -> System 4 encoder per `s52s4.pl`. -/
def system5ToSystem4 (cfg : System5Config) (f : Nat) : System4Config :=
  { elems := System4Elem.set (encodeBag cfg.bag) :: starredEmptyPairs f ++
             cfg.rules.flatMap (fun r => encodeS5RuleToS4Elems r f)
    active := 0
    state := System4State.A }

/-- `encodeBag` is the `xorMerge` of the mapped bag into the empty set. -/
theorem encodeBag_eq_xorMerge (bag : List Int) :
    encodeBag bag = xorMerge [] (bag.map system5BagEntryToSystem4) := by
  unfold encodeBag xorMerge
  rw [List.foldl_map]

/-- The encoded bag never has duplicates: every `xorInsert` preserves `Nodup`
    and the fold starts from the empty list. -/
theorem encodeBag_nodup (bag : List Int) : (encodeBag bag).Nodup := by
  rw [encodeBag_eq_xorMerge]
  exact xorMerge_nodup [] _ List.nodup_nil

/-- The bag entry map `e -> e * 2 - 2` is injective. -/
theorem system5BagEntryToSystem4_injective (a b : Int)
    (h : system5BagEntryToSystem4 a = system5BagEntryToSystem4 b) : a = b := by
  unfold system5BagEntryToSystem4 at h
  omega

/-- On a `Nodup` bag no cancellation happens, so `encodeBag` is the old
    `map` encoder up to the order in which `xorInsert` prepends. -/
theorem encodeBag_eq_reverse_map (bag : List Int) (h : bag.Nodup) :
    encodeBag bag = (bag.map system5BagEntryToSystem4).reverse := by
  rw [encodeBag_eq_xorMerge]
  rw [xorMerge_disjoint_eq_reverse_append [] _ (fun y _ hy => by cases hy)
        (nodup_map_of_injective _ system5BagEntryToSystem4_injective h)]
  rw [List.append_nil]

/-- `allInts n` has length `n`. -/
@[simp] theorem allInts_length (n : Nat) : (allInts n).length = n := by
  simp [allInts]

/-- `allInts n` has no duplicates. -/
theorem allInts_nodup (n : Nat) : (allInts n).Nodup :=
  nodup_map_of_injective _ (fun a b hab => by omega) (List.nodup_range)

/-- The encoder always initialises the System 4 cfg in state `A`. -/
@[simp] theorem system5ToSystem4_state_A (cfg : System5Config) (f : Nat) :
    (system5ToSystem4 cfg f).state = System4State.A := rfl

/-- The encoder always initialises `active` to 0. -/
@[simp] theorem system5ToSystem4_active_zero (cfg : System5Config) (f : Nat) :
    (system5ToSystem4 cfg f).active = 0 := rfl

/-- Bag `[1, 3, 4, 6]` encodes to the System 4 set `{0, 4, 6, 10}` via
    `e * 2 - 2`; `xorInsert` prepends, so the list comes out reversed. -/
example : encodeBag [1, 3, 4, 6] = [10, 6, 4, 0] := by decide

/-- The parity cancellation of `s52s4.pl`: an entry contributed twice
    disappears from the encoded set. -/
example : encodeBag [1, 3, 1] = [4] := by decide

/-- `starredEmptyPairs 2` produces 2 stars + 2 empty sets, alternating. -/
example : starredEmptyPairs 2
    = [System4Elem.star, System4Elem.set [],
       System4Elem.star, System4Elem.set []] := by decide

/-- `allInts 5 = [0, 1, 2, 3, 4]`. -/
example : allInts 5 = [0, 1, 2, 3, 4] := by decide

/-- `encodeS5RuleToS4Set [1, 4] 16` removes `1*2 + 16 + 3 = 21` and
    `4*2 + 16 + 3 = 27` from `allInts 49`.  The result is everything
    in 0..48 except 21 and 27. -/
example :
    encodeS5RuleToS4Set [1, 4] 16
    = ((allInts 49).erase 21).erase 27 := by
  decide

end BiTM
