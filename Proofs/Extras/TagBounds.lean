/-
  Extras.TagBounds

  The tag side of open item 1 (PLAN.md milestone M9), for the closed-form
  initial conditions only: the number of tag steps the tag system of
  `TagSystem.CockeMinsky` takes for `n` raw machine steps
  (`TagSystem.RawRuns`) has a closed-form bound. A round costs at most five
  passes over the word, whose halves are the numbers `val left` and
  `head + 2 val right`, below `2 ^ sz c` and `2 ^ (sz c + 1)`; a raw step
  grows the tape by at most one cell. Hence `roundLen c <= 15 * 2 ^ sz c`
  and `tagTime c n <= n * 15 * 2 ^ (sz c + n)` (`tagTime_le`), a bound
  computed from the size of the configuration and `n` only.

  Contents: `sz`, `sz_rawStep`, `val_lt_two_pow`, `roundLen_le`,
  `tagTime_le`.
-/

import Wolfram23.Infinite.RawRuns

namespace TagSystem

open TM
open BiTM

variable (tm : Machine)

/-! ## The closed-form bound -/

/-- The number of explicit cells of a configuration off the head. -/
def sz (c : Config) : Nat := c.left.length + c.right.length

theorem length_readHead_snd (l : List Nat) : (readHead l).2.length = l.length - 1 := by
  cases l <;> rfl

theorem sz_rawStep (c : Config) : sz (rawStep tm c) ≤ sz c + 1 := by
  unfold sz rawStep
  cases (tm.transition c.state c.head).dir <;>
    simp only [List.length_cons, length_readHead_snd] <;> omega

theorem sz_rawRun (c : Config) (n : Nat) : sz (rawRun tm c n) ≤ sz c + n := by
  induction n generalizing c with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have h1 := ih (rawStep tm c)
    have h2 := sz_rawStep tm c
    show sz (rawRun tm (rawStep tm c) n) ≤ _
    omega

theorem val_lt_two_pow (l : List Nat) (hl : ∀ a ∈ l, a < 2) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a List.mem_cons_self
    have := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    simp only [val_cons, List.length_cons, Nat.pow_succ]
    omega

theorem roundLen_le (c : Config) (hv : ValidCfg c) : roundLen tm c ≤ 15 * 2 ^ sz c := by
  obtain ⟨hh, hl, hr⟩ := hv
  have h1 := val_lt_two_pow c.left hl
  have h2 := val_lt_two_pow c.right hr
  have hL : 2 ^ c.left.length ≤ 2 ^ sz c := Nat.pow_le_pow_right (by omega) (by unfold sz; omega)
  have hR : 2 ^ c.right.length ≤ 2 ^ sz c := Nat.pow_le_pow_right (by omega) (by unfold sz; omega)
  have hsum : val c.left + (c.head + 2 * val c.right) + 2 ≤ 3 * 2 ^ sz c := by omega
  unfold roundLen
  cases (tm.transition c.state c.head).dir <;> simp only <;> omega

/-- The tag time of `n` raw steps from a valid configuration, bounded by the
    size of the configuration and `n` alone. -/
theorem tagTime_le (hwf : WF tm) (c : Config) (hv : ValidCfg c) (hst : c.state < tm.numStates)
    (n : Nat) : tagTime tm c n ≤ n * 15 * 2 ^ (sz c + n) := by
  induction n generalizing c with
  | zero => simp [tagTime]
  | succ n ih =>
    obtain ⟨hv1, hst1⟩ := rawStep_valid tm hwf c hv hst
    show roundLen tm c + tagTime tm (rawStep tm c) n ≤ _
    have h1 := roundLen_le tm c hv
    have h2 := ih (rawStep tm c) hv1 hst1
    have h3 : 2 ^ (sz (rawStep tm c) + n) ≤ 2 ^ (sz c + (n + 1)) :=
      Nat.pow_le_pow_right (by omega) (by have := sz_rawStep tm c; omega)
    have h4 : 2 ^ sz c ≤ 2 ^ (sz c + (n + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    have h5 : n * 15 * 2 ^ (sz (rawStep tm c) + n) ≤ n * 15 * 2 ^ (sz c + (n + 1)) :=
      Nat.mul_le_mul_left _ h3
    have e : (n + 1) * 15 * 2 ^ (sz c + (n + 1))
        = n * 15 * 2 ^ (sz c + (n + 1)) + 15 * 2 ^ (sz c + (n + 1)) := by
      rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega

end TagSystem
