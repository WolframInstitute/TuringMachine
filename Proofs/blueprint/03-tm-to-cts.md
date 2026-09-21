# 03. T7: from a binary Turing machine to a cyclic tag system

## Orientation

This link is independent of Smith's paper. It supplies what Smith's theorem consumes:
a two-colour cyclic tag system that simulates a given Turing machine, with a decoder.
It is a genuine construction, not an appeal to the literature: a 2-tag system after
Cocke and Minsky (1964; Minsky 1967, section 14.6) in a phase design of our own,
carried onto a finite alphabet, then onto a cyclic tag system by Cook's encoding
(`TagSystem/TagToCTS.lean`, which predates the rebuild and is used unchanged).

The class of machines is the binary machines: `[[TagSystem.WF]]` restricts the
transition table to bits and `[[TagSystem.ValidCfg]]` the tape to bits. A k-symbol
machine must be encoded in binary before this theorem applies; that reduction is not
formalized (chapter 11).

## Rounds of a 2-tag system

`TagSystem/TagRounds.lean` treats a 2-tag system over any alphabet: `[[TagSystem.stepP]] P`
reads the first symbol, deletes the first two and appends `P` of the symbol read;
`[[TagSystem.nStepsP]]` iterates. (`[[TagSystem.Tag.step]]` of `TagSystem/Basic.lean` is
`stepP ts.productions`, `[[TagSystem.Tag.step_eq_stepP]]`.)

A round processes the whole current word. `[[TagSystem.passOut]] P u` is the
concatenation of the productions of every other symbol of `u`, starting with the first.
Two facts describe a round:

```lean
theorem nStepsP_even (P : σ → List σ) (n : Nat) :
    ∀ (u t : List σ), u.length = 2 * n → nStepsP P (u ++ t) n = some (t ++ passOut P u)

theorem nStepsP_odd (P : σ → List σ) (n : Nat) (u : List σ) (z : σ) (hu : u.length = 2 * n)
    (hne : passOut P u ≠ []) :
    nStepsP P (u ++ [z]) (n + 1) = some ((passOut P (u ++ [z])).tail)
```

A word of even length is replaced by `passOut` of it in half as many steps. A word of
odd length reads its last symbol together with the first symbol of what was appended,
so the result is `passOut` of it without its first symbol: the frame of the next round
is shifted by one, and that round reads the second of every pair. This one dropped
symbol is the whole mechanism of the construction. The computation lemmas give
`passOut` on aligned pairs, on pairs read after a leading symbol
(`[[TagSystem.passOut_cons_pairs2]]`) and on runs of one symbol
(`[[TagSystem.passOut_cons_replicate_append]]`: a symbol, half the run rounded down,
then the rest read from its first or second symbol by the run's parity).

## The Cocke-Minsky construction

`TagSystem/CockeMinsky.lean`. The configuration `(q, left, head, right)` of the machine
is the word

    A_q x (al_q x)^m B_q x (be_q x)^N,   m = val left,  N = head + 2 * val right,

`[[TagSystem.cword]]` and `[[TagSystem.word]]`, with `[[TagSystem.val]]` reading a tape half
as a number, nearest cell least significant. The scanned cell is the lowest bit of the
right number. Symbols (`[[TagSystem.Sym]]`) carry a kind (`[[TagSystem.Kind]]`, 21 kinds),
a state and two bits; `x` is the pad. One machine step is three or five rounds of the
tag system with productions `[[TagSystem.prod]]`:

- round 1 (`A -> P1 P0`, `al -> p p`, `B -> Q`, `be -> r`) leaves `P1 P0 (p p)^m Q r^N`,
  whose length has the parity of `N + 1` (`[[TagSystem.round1]]`);
- round 2 reads `P1`, `m` of the `p`, `Q` and `N / 2` of the `r`, producing pairs
  `E1 E0 (e1 e0)^m F1 F0 (f1 f0)^(N/2)`; when `N` is even the round has odd length, its
  last read takes `E1` as its deleted partner, and round 3 reads the second of every
  pair: every symbol read in round 3 knows the scanned bit `h = N mod 2`, and `N` has
  lost its lowest bit (`[[TagSystem.round2]]`);
- round 3 executes the transition `(q, h) -> (q', w, d)`. For a move to the right the
  next configuration word is written directly, `A_q' x (al x)^(w + 2m) B x (be x)^(N/2)`
  (`[[TagSystem.round3R]]`). For a move to the left round 3 writes `G g^m H H k^(4 (N/2))`
  (`[[TagSystem.round3L]]`), round 4 halves `m` and reads its parity into the frame of
  round 5 (`[[TagSystem.round4]]`), and round 5 writes
  `A_q' x (al x)^(m/2) B x (be x)^(2w + (m mod 2) + 4 (N/2))` (`[[TagSystem.round5]]`).

Whenever a round reads the second of each pair, the production of the first symbol
read carries a leading pad `x` that the odd round before it consumes, so the tag word at
the start of every machine step is exactly the configuration word:

```lean
theorem tm_step_tag (c c' : Config) (hv : ValidCfg c)
    (hb : (tm.transition c.state c.head).write < 2) (hs : BiTM.step tm c = some c') :
    ∃ k, 1 ≤ k ∧ nStepsP (prod tm) (word c) k = some (word c')
```

The step counts are explicit in the proof (three rounds of `m + N + 2`, `m + N/2 + 2`,
`m + N/2 + 2` steps for a move to the right; five for a move to the left). They grow with
the numbers `m` and `N`, that is, exponentially in the tape length. The construction was
validated by a Python simulation of random machines before it was proved.

## The finite alphabet and the cyclic tag system

`TagSystem/TMToCTS.lean`. `[[TagSystem.enc]] S` sends the symbols whose state is below
`S` injectively into `Fin (1 + 84 * S)` and `[[TagSystem.dec]]` inverts it
(`[[TagSystem.dec_enc]]`). `[[TagSystem.WordOK]]` says all states of a word are below `S`;
the productions preserve it when the transitions do (`[[TagSystem.prod_OK]]`), and
`[[TagSystem.nStepsP_enc]]` carries runs over. `[[TagSystem.tagK]] tm S` is the resulting
`Tag (1 + 84 * S)`.

Cook's encoding `[[TagSystem.tagToCTS]]` turns a tag system on `k` symbols into a cyclic
tag system with `2k` appendants: symbol `i` is the one-hot word of length `k`, the first
`k` appendants are the encoded productions, the next `k` are empty (they consume the
second deleted symbol). One tag step is `2k` cyclic tag steps
(`[[TagSystem.tagToCTS_simulation]]`), and `[[TagSystem.cts_of_tag]]` iterates this.

```lean
def WF (tm : Machine) : Prop :=
  ∀ q, q < tm.numStates → ∀ s, s < 2 →
    (tm.transition q s).write < 2 ∧ (tm.transition q s).nextState < tm.numStates

def ValidCfg (c : Config) : Prop := c.head < 2 ∧ (∀ a ∈ c.left, a < 2) ∧ (∀ a ∈ c.right, a < 2)

def ctsOfCfg (S : Nat) (c : Config) : CTSConfig :=
  tagConfigToCTS (1 + 84 * S) ((word c).map (enc S))

theorem tm_cts_forwardSim (hwf : WF tm) :
    ForwardSim (tmSys tm) (ctsSys (tagToCTS (tagK tm tm.numStates) (K_pos _)))
      (fun c d => ValidCfg c ∧ c.state < tm.numStates ∧ d = ctsOfCfg tm.numStates c)

theorem tm_tag_forwardSim (hwf : WF tm) :
    ForwardSim (tmSys tm) (tagSysK tm tm.numStates)
      (fun c w => ValidCfg c ∧ c.state < tm.numStates ∧ w = (word c).map (enc tm.numStates))
```

The tag-level simulation `[[TagSystem.tm_tag_forwardSim]]` is what chapter 09 uses,
because the number of cyclic tag cycles must be the number of tag steps.

## The decoder

`[[TagSystem.decodeCTS]] S d` reads the one-hot blocks of the cyclic tag word back as tag
symbols (`[[TagSystem.tagWordDecode]]`), the symbols as a configuration word
(`[[TagSystem.parseWord]]`, counting the pairs), and the two numbers as tape halves
(`[[TagSystem.natBits]]`, the binary digits without trailing zeros). It returns the
configuration without trailing blanks:

```lean
def canon (c : Config) : Config := ⟨c.state, natBits (val c.left), c.head, natBits (val c.right)⟩

theorem decodeCTS_word (S : Nat) (c : Config) (hv : ValidCfg c) (hst : c.state < S) :
    decodeCTS S (ctsOfCfg S c) = some (canon c)
```

T7 in the finite form shared by every link:

```lean
theorem t7_finite (hwf : WF tm) (c : Config) (hv : ValidCfg c) (hst : c.state < tm.numStates)
    (n : Nat) (c' : Config) (hrun : BiTM.nSteps tm c n = some c') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ i, i < n → times i < times (i + 1)) ∧
      ∀ i, i ≤ n → ∃ ci di, BiTM.nSteps tm c i = some ci ∧
        (tagToCTS (tagK tm tm.numStates) (K_pos _)).nSteps (ctsOfCfg tm.numStates c) (times i)
          = some di ∧
        decodeCTS tm.numStates di = some (canon ci)
```

## Notes and caveats

- Binary machines only. `WF` quantifies over `s < 2` and never reads `numSymbols`; a
  machine with `numSymbols := 17` and junk on symbols 2 and up is `WF` if its bit rows
  are. The docs of `docs/PLAN.md` section 2 that say "every well-formed TM" overstate
  this (chapter 11).
- The halt row. `[[BiTM.step]]` returns `none` in state 0 before consulting the table,
  but `WF` requires the row of state 0 to be in range, because the tag productions keep
  applying `tm.transition 0 _` after the machine has halted and `prod_OK` needs the
  states to stay bounded. A machine whose halt row is out of range can be patched
  without changing any run; the wrapper lemma is not written (chapter 11).
- The tag system is stated for machine steps only; a halted machine makes none, and
  nothing relates the tag system's own halting to the machine's.
- `decodeCTS` is proved complete (it inverts the encoder: `[[TagSystem.decodeCTS_word]]`),
  and its block stage is also sound since 2026-09-22: `[[TagSystem.symbolDecode]]` accepts
  exactly the one-hot blocks of length `k` (`[[TagSystem.symbolDecode_sound]]`) and
  `[[TagSystem.tagWordDecode]]` exactly their concatenations
  (`[[TagSystem.tagWordDecode_sound]]`), so a word with a short last block or a stray bit
  is rejected. The later stages (`decodeWord`, `cfgOfNums`) are used for completeness
  only. Only completeness is used by the headline.
- The header of `TagSystem/TagToCTS.lean` used to say the cyclic tag system has `k`
  appendants; the definition and its lemma say `2k` (the header does too since
  2026-09-22), and the factor 2 is load-bearing in chapter 09.

## Depends on

`TagSystem.Basic`, `TagSystem.TagRounds`, `TagSystem.CockeMinsky`, `TagSystem.TagToCTS`,
`TagSystem.TMToCTS`, `Smith.Simulation` (for `ForwardSim`), `BiTM.Basic`.
