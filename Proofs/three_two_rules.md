# (3,2) One-Sided Turing Machines: Binary Successor Analysis

## Search Results

From the full (3,2) rule space (~3M rules), `OneSidedTuringMachineFind` identified:

| Category | Count | Description |
|----------|-------|-------------|
| Total candidates | 8,934 | Match +1 for inputs 1..20 (halt or non-halt) |
| Always-halting | 6,771 | Halt with correct output for ALL inputs 1..20 |
| Partial | 2,163 | Non-halt on ≥1 input in 1..20 |
| Step profiles | 160 | Distinct behavioral classes |

## Key Findings

### No Genuine Late Failures

All **6,771 always-halting rules** were tested on inputs 1..2000 with 100K step bounds:
**Zero failures.** Every rule that halts correctly for 1..20 also halts correctly for 1..2000.

This is a strong empirical result: in the (3,2) space, passing inputs 1..20 appears sufficient
to identify genuinely correct successor machines.

### Near-Miss Analysis

Among the 2,163 partial rules (matching some but not all inputs), the **longest strict correct prefix**
(consecutive correct+halting results starting from n=1) is **6** — achieved by **Rule 156830**.

### Rule 156830: The Best Near-Miss

**Transition table:**
```
(1,0) → state 2, write 1, R    (1,1) → state 1, write 0, L
(2,0) → state 3, write 0, R    (2,1) → state 2, write 1, L
(3,0) → state 1, write 0, R    (3,1) → state 2, write 0, L
```

**Behavior:**
- ✅ Correct for inputs 1..6 (verified in Lean 4)
- ❌ **Fails at n=7**: outputs 9 instead of 8
- ❌ Also fails at n=15: outputs 18 instead of 16

**Failure mechanism** — carry-propagation overflow:
- For inputs ending in ≤2 consecutive 1-bits (e.g. 3=11, 5=101), the carry propagates correctly
- For 7=111 (3 consecutive 1-bits), the machine correctly flips all three to 0 and writes a 1
  at position 3 (value=8), but then the head bounces back to position 0 in state 1, causing an
  extra 1 to be written → value becomes 9=1001 instead of 8=1000

### Classification of the 2,163 Partial Rules

By first non-halting input:

| First non-halt at | Count | Pattern |
|-------------------|-------|---------|
| n=1 | 1,755 | Don't halt on simplest odd input |
| n=3 | 390 | Handle n=1,2 but fail at 3=11 |
| n=5 | 13 | Handle up to 4 |
| n=7 | 4 | Handle up to 6 |
| n=15 | 1 | Rule 151665, handles up to 14 |

## Formal Proofs

### NearMiss.lean (NEW)

| Theorem | Statement |
|---------|-----------|
| `nearMiss_correct_1_to_6` | Rule 156830 correctly computes n+1 for all n ∈ {1..6} |
| `nearMiss_not_successor` | Rule 156830 does NOT compute the successor function (fails at n=7) |
| `nearMiss_fails_at_15` | Also fails at n=15 |

### Basic.lean (EXTENDED)

| Theorem | Statement |
|---------|-----------|
| `eval_mono` | If eval halts at fuel f, it halts with the same result at fuel f+k |
| `eval_det` | Eval is deterministic: halted config is unique regardless of fuel amount |

The `eval_det` theorem is the key infrastructure for proving that a TM does NOT compute
a function: if we know the unique halted config (by `native_decide`), we can derive any
property of it (including contradiction with wrong output values).
