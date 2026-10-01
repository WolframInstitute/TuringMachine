# Archive

These files are the April-May 2026 exploratory development of the Wolfram (2,3)
universality formalization. They are kept for reference only: they are NOT in
the lakefile roots and are NOT built. Four `sorry` sites survive here
(`SmithChain.lean` x3, `CockeMinskyConstruction.lean` x1); none of them can be
closed, because each sits under a statement that is false or unsatisfiable.
Nothing outside `Archive/` imports anything in `Archive/`.

The reasons below are condensed from `docs/REVIEW.md` sections 4 and 6.

## BiTM/

- `SmithChain.lean` - the Conjecture 5 emulation theorems
  (`ctsToSystem5_emulates`, `ctsToSystem5_emulates_with_budget`) are false as
  stated and type-check only because `smith_per_step_extension` is sorry'd;
  `SmithReducesFaithful` and `SmithChainEmulators` are unsatisfiable, so the
  eight theorems conditioned on them are vacuous at `wolfram23`.
- `CockeMinsky.lean` - `IsUniversal` is provably equivalent to `True`, and
  `wolfram23_universal` composes two constant encoders; `IsSubstantiallyUniversal`
  is false for `wolfram23`.
- `CockeMinskyConstruction.lean` - `CockeMinskyReducesFaithful` is satisfied for
  every machine by a halting oracle (the encoder branches on `Halts tm cfg` with
  `Classical.choose`), and the concrete Minsky-style encoder `cmStep_sim` is
  sorry'd and false as defined.
- `Smith.lean` - `SmithReducesStepFaithful` is false: `selfLoopCTS` forces a
  periodic `wolfram23` configuration, and `wolfram23` has none (Smith, PDF
  p.21-22). The file treats loop-freeness as an open question, which reverses
  the sign of Smith's key lemma.
- `System1.lean` - Smith's System 1 reads the active cell and its right
  neighbour. This file models the neighbour cases as extra tape symbols with
  halting placeholders, so `system1` is `wolfram23` relabelled and the lock-step
  theorems are true of the relabelling, not of System 1.
- `GeneralizedTM.lean` - the machine type reads a single cell, so it cannot
  express Smith's Systems 1-3 at all.
- `Wolfram23Periodic.lean` - dead weight: no module imports it.
- `CTSToSystem5.lean` - the 19,305-line original. Its encoder definitions and
  structural lemmas were salvaged into the slim `BiTM/CTSToSystem5.lean` that
  stays in the build; the rest is a corollary treadmill, including about 60
  theorems under the unsatisfiable hypothesis
  `not (System5.Halts (ctsToSystem5 ...))`, a Perm-chain family that re-encodes
  the rule queue fresh at every chain point and ignores `cfg.phase`, the
  AllEmptyAppendants family (CTSs that never append anything), the schematic
  bags, and `ctsToSystem5_halt_preservation`, which is closed with `N := 0`.
