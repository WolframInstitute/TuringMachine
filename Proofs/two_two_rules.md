# (2,2) One-Sided TM Binary Successor: Complete Analysis

## Overview

Among all 2-state, 2-symbol one-sided Turing machines, exactly **17 rules** compute the binary successor function (`n → n + 1`). These partition into **3 behaviorally distinct classes** despite having different transition tables.

## Rule Classes

### Class A (1 rule)
**Rule 445**: `(1,0)→(2,1,L) (1,1)→(1,0,L) (2,0)→(2,0,R) (2,1)→(2,0,R)`

Unique algorithm: scans left writing 0s (carry propagation), then appends 1 at the boundary and returns rightward clearing.

### Class B (8 rules: 453, 461, 469, 477, 485, 493, 501, 509)
All share the behavioral structure via `IsClassB`:
- `(1,0) → (2,1,R)` — absorb: write 1, go right (toward index 0)
- `(1,1) → (1,0,L)` — flip: write 0, go left (continue scanning)
- `(2,1) → (2,0,R)` — clear1: clear trailing 1s on return

The `(2,0)` transition is **dead** — never reached during computation. The 8 variants arise from all possible `(2,0)` transitions.

**Algorithm**: Scan left flipping 1→0 (carry propagation). On first 0: absorb (0→1) and reverse direction. Return rightward clearing all modified 1-bits to 0. Result: standard binary +1.

### Class C (8 rules: 1512-1519)
All share the behavioral structure via `IsClassC`:
- `(1,0) → (2,1,R)` — absorb: write 1, go right
- `(1,1) → (1,1,L)` — skip: identity write, go left (scan past 1s)
- `(2,1) → (2,0,R)` — clear1: clear trailing 1s on return

The `(2,0)` transition is **dead**. The 8 variants arise from all possible `(2,0)` transitions.

**Algorithm**: Scan left skipping 1s (no modification). On first 0: absorb (0→1) and reverse direction. Return rightward clearing ALL ones (including the prefix) to 0. Result: standard binary +1.

## Key Insight: Equivalence via Dead Transitions

All 16 non-445 rules differ only in the `(2,0)` transition, which is never reached. This means:
- Rules within each class are **computationally identical** for the +1 function
- The (2,0) transition creates the combinatorial explosion: 8 possible `(state, write, dir)` triples × 2 classes = 16 rules

## Formal Verification

All 17 rules are proven to compute binary successor in Lean 4:

| Component | File | Approach |
|-----------|------|----------|
| Class A (rule 445) | `PlusOne.lean` | Direct `native_decide` |
| Class B (8 rules) | `AllPlusOne.lean` | `IsClassB` + `sim_eval_B` + `return_zeros` |
| Class C (8 rules) | `ClassC.lean` | `IsClassC` + `sim_eval_C` + `return_clear_ones` |
| Computational check | `AllPlusOne.lean` | All 17 verified for n=1..65535 |

**Build**: `lake clean && lake build` — zero errors, zero sorrys.
