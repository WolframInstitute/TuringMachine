/- Temporary lemma test for write/read -/
import OneSidedTM.Basic
import OneSidedTM.ClassB

open OneSidedTM

lemma read_write_other (tape : List Nat) (i j v : Nat) (h : i ≠ j) :
    readTape (writeTape tape i v) j = readTape tape j := by
  simp [readTape, writeTape, List.getD]
  split
  · simp [List.getD, List.get?_set]
    split <;> omega
  · simp [List.getD, List.get?_append]

