use num_traits::ToPrimitive;
// Direct dep only for wolfram_library_link::aborted() (kernel-abort checks in
// the long-running searches). default-features off keeps the WSTP C++ stack
// out of the build, which would not cross-compile to macOS under Zig.
use wolfram_library_link as wll;

use crate::models::{TMState, Tape, TuringMachine, Rule};
use num_bigint::{BigInt, BigUint};
use std::collections::{HashMap, HashSet, VecDeque};
use std::collections::BinaryHeap;
use rayon::prelude::*;

pub mod models;
/// Build a table of deterministic TM outputs:
/// Rows correspond to rule numbers 0 .. (2*s*k)^(s*k) - 1
/// Columns correspond to input tape integers 0 .. max_input
/// Each cell is Some(BigUint) if machine halts within max_steps, else None.
pub fn dtm_output_table(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<Vec<Option<BigUint>>> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp); // (2*s*k)^(s*k)
    let mut table: Vec<Vec<Option<BigUint>>> = Vec::with_capacity(rule_space_size as usize);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    for rule_num in min_rule..=max_rule {
        if aborted_safe() { break; }
        let n_bigint = BigInt::from(rule_num);
        let tm = match models::TuringMachine::from_number(&n_bigint, num_states, num_symbols) {
            Ok(t) => t,
            Err(_) => { table.push(Vec::new()); continue; }
        };
    if min_input > max_input { table.push(Vec::new()); continue; }
    let mut row: Vec<Option<BigUint>> = Vec::with_capacity((max_input - min_input + 1) as usize);
    for input in min_input..=max_input {
            if aborted_safe() { break; }
            let input_big = BigUint::from(input);
            let result = run_dtm(&tm, &input_big, max_steps).map(|(_steps, output, _maxw)| output);
            row.push(result);
        }
        table.push(row);
    }
    table
}

/// Parallel version of dtm_output_table using rayon; preserves row ordering.
pub fn dtm_output_table_parallel(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<Vec<Option<BigUint>>> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_parallel_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}

/// Variant that preserves both halting step count and output value.
/// Each cell: Some((steps, output)) if halts within max_steps else None.
pub fn dtm_output_table_triple(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<Vec<Option<(u64, BigUint, u64)>>> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_triple_parallel_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}

/// Parallel version of dtm_output_table_steps_width using rayon.
pub fn dtm_output_table_triple_parallel(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<Vec<Option<(u64, BigUint, u64)>>> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_triple_parallel_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}

/// Variant that returns complete evolution history for each (rule, input) pair.
/// Each cell is a Vec of (state, head_position, tape_value) for each step.
/// Empty vector indicates the machine didn't halt within max_steps.
pub fn dtm_output_table_triple_with_history(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<Vec<Vec<(u32, usize, BigUint)>>> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_triple_with_history_parallel_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}

/// Parallel version of dtm_output_table_triple_with_history using rayon.
pub fn dtm_output_table_triple_with_history_parallel(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<Vec<Vec<(u32, usize, BigUint)>>> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_triple_with_history_parallel_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}


/// Parallel version returning contiguous array of f64 pairs (step, value), {0.0, 0.0} for non-halting cases.
pub fn dtm_output_table_pair_parallel_f64(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<f64> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_pair_parallel_f64_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}

/// Parallel version returning just halting steps as u64 (0 for non-halting) flattened row-major.
pub fn dtm_output_table_parallel_steps_u64(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<u64> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_parallel_steps_u64_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}

/// Parallel version returning just maximum head width (max head position reached) as u64 (0 for non-halting) flattened row-major.
pub fn dtm_output_table_parallel_width_u64(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<u64> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_parallel_width_u64_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}

/// Parallel version returning flattened pairs of (steps, width) as u64.
/// Non-halting entries are (0, 0).
pub fn dtm_output_table_parallel_steps_width_u64(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<u64> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_parallel_steps_width_u64_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}

/// Parallel version returning (steps, value) pairs with full precision (BigUint values).
/// Each cell: Some((steps, output)) if halts within max_steps, else None.
pub fn dtm_output_table_parallel_steps_value(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<Vec<Option<(u64, BigUint)>>> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_parallel_steps_value_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}

/// Parallel version returning contiguous array of f64 triples (step, value, width), {0.0, -1.0, 0.0} for non-halting cases.
pub fn dtm_output_table_triple_parallel_f64(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> Vec<f64> {
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    if min_input > max_input { return Vec::new(); }
    let rules: Vec<BigInt> = (min_rule..=max_rule).map(BigInt::from).collect();
    let inputs: Vec<BigUint> = (min_input..=max_input).map(BigUint::from).collect();
    dtm_output_table_triple_parallel_f64_vec(num_states, num_symbols, max_steps, &rules, &inputs)
}

// =============================================================================
// Vector-based variants: accept explicit Vec<u64> for rules and Vec<u32> for inputs
// =============================================================================

/// Parallel version returning Option<BigUint> for explicit vectors of rules and inputs.
pub fn dtm_output_table_parallel_vec(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: &[BigInt],
    inputs: &[BigUint],
) -> Vec<Vec<Option<BigUint>>> {
    rules
        .par_iter()
        .map(|rule_num| {
            let tm = match models::TuringMachine::from_number(rule_num, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return inputs.iter().map(|_| None).collect(),
            };
            inputs
                .iter()
                .map(|input| {
                    match run_dtm(&tm, input, max_steps) {
                        Some((_, val, _)) => Some(val),
                        None => None
                    }
                })
                .collect()
        })
        .collect()
}

/// Parallel version returning (steps, output, width) triples for explicit vectors.
pub fn dtm_output_table_triple_parallel_vec(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: &[BigInt],
    inputs: &[BigUint],
) -> Vec<Vec<Option<(u64, BigUint, u64)>>> {
    rules
        .par_iter()
        .map(|rule_num| {
            let tm = match models::TuringMachine::from_number(rule_num, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return inputs.iter().map(|_| None).collect(),
            };
            inputs
                .iter()
                .map(|input| run_dtm(&tm, input, max_steps))
                .collect()
        })
        .collect()
}

/// Parallel version returning halting steps as u64 for explicit vectors.
pub fn dtm_output_table_parallel_steps_u64_vec(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: &[BigInt],
    inputs: &[BigUint],
) -> Vec<u64> {
    let num_inputs = inputs.len();
    let rows: Vec<Vec<u64>> = rules
        .par_iter()
        .map(|rule_num| {
            let tm = match models::TuringMachine::from_number(rule_num, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return vec![0u64; num_inputs],
            };
            inputs
                .iter()
                .map(|input| {
                    match run_dtm(&tm, input, max_steps) {
                        Some((steps, _, _)) => steps,
                        None => 0
                    }
                })
                .collect()
        })
        .collect();
    rows.into_iter().flatten().collect()
}

/// Parallel version returning max head width as u64 for explicit vectors.
pub fn dtm_output_table_parallel_width_u64_vec(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: &[BigInt],
    inputs: &[BigUint],
) -> Vec<u64> {
    let num_inputs = inputs.len();
    let rows: Vec<Vec<u64>> = rules
        .par_iter()
        .map(|rule_num| {
            let tm = match models::TuringMachine::from_number(rule_num, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return vec![0u64; num_inputs],
            };
            inputs
                .iter()
                .map(|input| {
                    match run_dtm(&tm, input, max_steps) {
                        Some((_, _, pos)) => pos + 1,
                        None => 0
                    }
                })
                .collect()
        })
        .collect();
    rows.into_iter().flatten().collect()
}

/// Parallel version returning (steps, width) pairs for explicit vectors.
pub fn dtm_output_table_parallel_steps_width_u64_vec(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: &[BigInt],
    inputs: &[BigUint],
) -> Vec<u64> {
    let num_inputs = inputs.len();
    let rows: Vec<Vec<u64>> = rules
        .par_iter()
        .map(|rule_num| {
            let tm = match models::TuringMachine::from_number(rule_num, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return vec![0u64; num_inputs * 2],
            };
            inputs
                .iter()
                .flat_map(|input| {
                    match run_dtm(&tm, input, max_steps) {
                        Some((steps, _, pos)) => vec![steps, pos + 1],
                        None => vec![0u64, 0u64]
                    }
                })
                .collect()
        })
        .collect();
    rows.into_iter().flatten().collect()
}

/// Parallel version returning f64 pairs (step, value) for explicit vectors.
pub fn dtm_output_table_pair_parallel_f64_vec(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: &[BigInt],
    inputs: &[BigUint],
) -> Vec<f64> {
    let num_inputs = inputs.len();
    let rows: Vec<Vec<f64>> = rules
        .par_iter()
        .map(|rule_num| {
            let tm = match models::TuringMachine::from_number(rule_num, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return vec![0.0; num_inputs * 2],
            };
            inputs
                .iter()
                .flat_map(|input| {
                    match run_dtm(&tm, input, max_steps) {
                        Some((steps, val, _)) => {
                            let val_f64 = val.to_f64().unwrap_or(f64::NAN);
                            vec![steps as f64, val_f64]
                        },
                        None => vec![0.0, 0.0]
                    }
                })
                .collect()
        })
        .collect();
    rows.into_iter().flatten().collect()
}

/// Parallel version returning (steps, value) pairs with full precision for explicit vectors.
pub fn dtm_output_table_parallel_steps_value_vec(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: &[BigInt],
    inputs: &[BigUint],
) -> Vec<Vec<Option<(u64, BigUint)>>> {
    rules
        .par_iter()
        .map(|rule_num| {
            let tm = match models::TuringMachine::from_number(rule_num, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return inputs.iter().map(|_| None).collect(),
            };
            inputs
                .iter()
                .map(|input| {
                    match run_dtm(&tm, input, max_steps) {
                        Some((steps, val, _)) => Some((steps, val)),
                        None => None
                    }
                })
                .collect()
        })
        .collect()
}

/// Parallel version returning f64 triples (step, value, width) for explicit vectors.
pub fn dtm_output_table_triple_parallel_f64_vec(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: &[BigInt],
    inputs: &[BigUint],
) -> Vec<f64> {
    let num_inputs = inputs.len();
    let rows: Vec<Vec<f64>> = rules
        .par_iter()
        .map(|rule_num| {
            let tm = match models::TuringMachine::from_number(rule_num, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return vec![0.0; num_inputs * 3],
            };
            inputs
                .iter()
                .flat_map(|input| {
                    match run_dtm(&tm, input, max_steps) {
                        Some((steps, val, pos)) => {
                            let val_f64 = val.to_f64().unwrap_or(f64::NAN);
                            vec![steps as f64, val_f64, (pos + 1) as f64]
                        },
                        None => vec![0.0, 0.0, 0.0]
                    }
                })
                .collect()
        })
        .collect();
    rows.into_iter().flatten().collect()
}

/// Parallel version returning history for explicit vectors.
pub fn dtm_output_table_triple_with_history_parallel_vec(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: &[BigInt],
    inputs: &[BigUint],
) -> Vec<Vec<Vec<(u32, usize, BigUint)>>> {
    rules
        .par_iter()
        .map(|rule_num| {
            let tm = match models::TuringMachine::from_number(rule_num, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return inputs.iter().map(|_| Vec::new()).collect(),
            };
            inputs
                .iter()
                .map(|input| {
                    run_dtm_with_history(&tm, input, max_steps)
                })
                .collect()
        })
        .collect()
}


// Provide a safe wrapper for abort checks that tolerates tests (no WL init)
#[inline]
fn aborted_safe() -> bool {
    if cfg!(test) { return false; }
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use std::sync::atomic::{AtomicBool, Ordering};
    static AVAILABLE: AtomicBool = AtomicBool::new(false);
    static TRIED_ONCE: AtomicBool = AtomicBool::new(false);
    if AVAILABLE.load(Ordering::Relaxed) { return wll::aborted(); }
    if TRIED_ONCE.load(Ordering::Relaxed) { return false; }
    TRIED_ONCE.store(true, Ordering::Relaxed);
    match catch_unwind(AssertUnwindSafe(|| wll::aborted())) {
        Ok(v) => { AVAILABLE.store(true, Ordering::Relaxed); v }
        Err(_) => false,
    }
}

/// Sequential exhaustive search for target value using non-deterministic TM.
/// Returns Some(path) of rule numbers leading to target or None if not found within max_steps.
/// Seeds the queue with all initial values in `initials`.
/// Terminates early if any target in `targets` is found.
pub fn exhaustive_search_seq(
    tm: &TuringMachine,
    initials: &[BigUint],
    targets: &[BigUint],
    max_steps: u64,
) -> Option<Vec<u64>> {
    // Seed queue with all initial states
    let mut queue: VecDeque<(TMState, u64)> = VecDeque::new();
    let mut expanded: HashMap<TMState, (Option<TMState>, Option<u64>)> = HashMap::new();
    for initial in initials {
        let initial_tape = Tape::from_integer(initial);
        let initial_state = TMState {
            head_state: 1,
            head_position: 0,
            tape: initial_tape,
        };
        queue.push_back((initial_state.clone(), 0));
        expanded.insert(initial_state, (None, None));
    }
    // Build target set for fast lookup
    let target_set: HashSet<&BigUint> = targets.iter().collect();
    let mut seen_values: HashSet<BigUint> = HashSet::new();

    while let Some((current_state, depth)) = queue.pop_front() {
        // Cooperative abort: exit early if WL requested abort
        if aborted_safe() {
            return None;
        }
        let step = depth + 1;
        for (new_state, rule_num, halted) in tm.ndtm_step(&current_state) {
            if halted {
                let new_val = new_state.tape.to_integer();
                if seen_values.insert(new_val.clone()) {
                    if target_set.contains(&new_val) {
                        let mut path = reconstruct_path(&expanded, current_state);
                        path.push(rule_num);
                        return Some(path);
                    }
                }
            } else {
                if step < max_steps {
                    if expanded.contains_key(&new_state) {
                        continue;
                    }
                    expanded.insert(
                        new_state.clone(),
                        (Some(current_state.clone()), Some(rule_num)),
                    );
                    queue.push_back((new_state, depth + 1));
                }
            }
        }
    }
    None
}

/// Parallel exhaustive search (breadth-wise) using rayon. Returns first path found.
/// Seeds the heap with all initial values in `initials`.
/// Terminates early if any target in `targets` is found.
pub fn exhaustive_search_parallel(
    tm: &TuringMachine,
    initials: &[BigUint],
    targets: &[BigUint],
    max_steps: u64,
) -> Option<Vec<u64>> {
    use std::sync::{Arc, Mutex, atomic::{AtomicBool, AtomicUsize, Ordering}};
    use std::cmp::Ordering as CmpOrdering;
    #[derive(Clone)]
    struct ScoredState {
        score: usize, // lower is better (bit difference)
        depth: u64,
        state: TMState,
        path: Vec<u64>,
    }
    impl PartialEq for ScoredState { fn eq(&self, other: &Self) -> bool { self.score == other.score && self.depth == other.depth } }
    impl Eq for ScoredState {}
    impl PartialOrd for ScoredState { fn partial_cmp(&self, other: &Self) -> Option<CmpOrdering> { Some(self.cmp(other)) } }
    impl Ord for ScoredState { fn cmp(&self, other: &Self) -> CmpOrdering { // reverse for min-heap behavior via BinaryHeap (max-heap)
            other.score.cmp(&self.score).then_with(|| self.depth.cmp(&other.depth))
        } }
    // Compute bit difference heuristic between current tape value and closest target.
    fn min_bit_diff(a: &BigUint, targets: &[BigUint]) -> usize {
        use num_traits::Zero;
        targets.iter().map(|b| {
            if a.is_zero() { return b.bits() as usize; }
            if b.is_zero() { return a.bits() as usize; }
            let xor = a ^ b;
            xor.bits() as usize
        }).min().unwrap_or(usize::MAX)
    }
    // Build target set for fast lookup
    let target_set: HashSet<BigUint> = targets.iter().cloned().collect();
    let targets_vec: Vec<BigUint> = targets.to_vec();
    
    let heap: Arc<Mutex<BinaryHeap<ScoredState>>> = Arc::new(Mutex::new(BinaryHeap::new()));
    // Seed heap with all initial states
    for initial in initials {
        let initial_tape = Tape::from_integer(initial);
        let initial_state = TMState { head_state: 1, head_position: 0, tape: initial_tape };
        let initial_val = initial_state.tape.to_integer();
        let score = min_bit_diff(&initial_val, &targets_vec);
        heap.lock().unwrap().push(ScoredState { score, depth: 0, state: initial_state, path: Vec::new() });
    }
    
    let expanded = Arc::new(Mutex::new(HashSet::new()));
    let found = Arc::new(AtomicBool::new(false));
    let active_workers = Arc::new(AtomicUsize::new(0));
    let result_path = Arc::new(Mutex::new(None));
    rayon::scope(|s| {
        for _ in 0..rayon::current_num_threads() {
            let heap = heap.clone();
            let expanded = expanded.clone();
            let found = found.clone();
            let result_path = result_path.clone();
            let tm = tm.clone();
            let target_set = target_set.clone();
            let targets_vec = targets_vec.clone();
            let active_workers = active_workers.clone();
            s.spawn(move |_| {
                while !found.load(Ordering::Relaxed) {
                    if aborted_safe() {
                        found.store(true, Ordering::Relaxed);
                        break;
                    }
                    let maybe_item = { heap.lock().unwrap().pop() };
                    if let Some(item) = maybe_item {
                        let ScoredState { score: _score, depth, state, path } = item;
                        active_workers.fetch_add(1, Ordering::SeqCst);
                        if depth >= max_steps {
                            active_workers.fetch_sub(1, Ordering::SeqCst);
                            continue;
                        }
                        {
                            let mut exp = expanded.lock().unwrap();
                            if exp.contains(&state) {
                                active_workers.fetch_sub(1, Ordering::SeqCst);
                                continue;
                            }
                            exp.insert(state.clone());
                        }
                        for (ns, rule_num, halted) in tm.ndtm_step(&state) {
                            let mut new_path = path.clone();
                            new_path.push(rule_num);
                            if halted {
                                let new_val = ns.tape.to_integer();
                                if target_set.contains(&new_val) {
                                    found.store(true, Ordering::SeqCst);
                                    *result_path.lock().unwrap() = Some(new_path);
                                    active_workers.fetch_sub(1, Ordering::SeqCst);
                                    break;
                                }
                            } else {
                                let new_val = ns.tape.to_integer();
                                let score = min_bit_diff(&new_val, &targets_vec);
                                heap.lock().unwrap().push(ScoredState { score, depth: depth+1, state: ns, path: new_path });
                            }
                        }
                        // Finished processing this popped state if target not found in its expansion
                        if !found.load(Ordering::Relaxed) {
                            active_workers.fetch_sub(1, Ordering::SeqCst);
                        }
                    } else {
                        // No work currently: termination detection
                        if heap.lock().unwrap().is_empty() && active_workers.load(Ordering::SeqCst) == 0 {
                            // Global exhaustion without finding target
                            found.store(true, Ordering::SeqCst);
                            break;
                        }
                        std::thread::yield_now();
                    }
                }
            });
        }
    });
    let out = result_path.lock().unwrap().clone();
    out
}

fn reconstruct_path(
    expanded: &HashMap<TMState, (Option<TMState>, Option<u64>)>,
    state: TMState,
) -> Vec<u64> {
    let mut path = Vec::new();
    let mut current = state;
    while let Some((parent, rule)) = expanded.get(&current) {
        if let Some(rule_num) = rule {
            path.push(*rule_num);
        }
        if let Some(parent_state) = parent {
            current = parent_state.clone();
        } else {
            break;
        }
    }
    path.reverse();
    path
}

pub fn run_dtm(
    tm: &TuringMachine,
    initial: &BigUint,
    max_steps: u64,
) -> Option<(u64, BigUint, u64)> {
    let initial_tape = Tape::from_integer_base(initial, tm.num_symbols);
    let mut state = TMState { head_state: 1, head_position: 0, tape: initial_tape };
    let mut steps: u64 = 0;
    // Track maximum absolute head position (distance from start) seen during evolution
    let mut max_head_pos: u64 = state.head_position as u64;

    // Optimization 1: If all deterministic rules move left, the machine will
    // forever drift left (or oscillate if left movement is clamped) without
    // reaching a halting configuration (given current halting semantics). Return None immediately.
    // (Assumes halting requires a rule transition evaluated during stepping; if such
    // a halting rule existed it would be encountered regardless of direction.)
    // Updated for Option<Rule>: if any variant is None (a deduplicated placeholder), we conservatively
    // disable the always-left optimization (treat as potentially right-moving) to avoid false halting.
    let always_left = tm.rules.iter().all(|variants| {
        variants.iter().all(|opt| match opt {
            Some(rule) => !rule.move_right,
            None => false, // unknown due to deduplication; be conservative
        })
    });
    if always_left { return None; }

    // Optimization 2 (heuristic): If the head has moved strictly right beyond max_steps - steps
    // before halting, we assume it will not halt within the remaining allotted steps.
    // This is a conservative early exit; rightward drift past max_steps implies any
    // potential halting transition would require > max_steps moves to revisit earlier cells.
    // We apply this check each iteration before performing the next step.

    while steps < max_steps {

        if state.head_position as u64 >= max_steps - steps { return None; }
        let halted = tm.step_dtm_mut(&mut state);
        // update max_head_pos after the step
        let cur_pos = state.head_position as u64;
        if cur_pos > max_head_pos { max_head_pos = cur_pos; }
        steps += 1;
        if halted {
            let output = state.tape.to_integer();
            return Some((steps, output, max_head_pos));
        }
    }
    None
}

/// Run a deterministic TM with history tracking.
/// Returns a Vec of (state, head_position, tape_value) for each step.
pub fn run_dtm_with_history(
    tm: &TuringMachine,
    initial: &BigUint,
    max_steps: u64,
) -> Vec<(u32, usize, BigUint)> {
    let initial_tape = Tape::from_integer_base(initial, tm.num_symbols);
    let mut state = TMState { head_state: 1, head_position: 0, tape: initial_tape };
    let mut steps: u64 = 0;
    let mut history: Vec<(u32, usize, BigUint)> = Vec::new();
    history.push((state.head_state, state.head_position + 1, state.tape.to_integer()));

    while steps < max_steps {

        let current_symbol = state.tape.read(state.head_position);
        if let Some(rule) = tm.get_rule(state.head_state, current_symbol) {
            state.tape.write(state.head_position, rule.write_symbol);
            let next_state = rule.next_state;
            let tape_value = state.tape.to_integer();
            
            state.head_state = next_state;
            let halted = if rule.move_right {
                if state.head_position == 0 {
                    true
                } else {
                    state.head_position -= 1;
                    false
                }
            } else {
                state.head_position += 1;
                false
            };

            steps += 1;
            if halted {
                history.push((next_state, 0, tape_value));
                return history;
            } else {
                history.push((next_state, state.head_position + 1, tape_value));
            }
        } else {
            return history;
        }
    }
    history
}

/// Traverse the non-deterministic TM and collect all unique halted tape values encountered.
/// No path information is retained; traversal stops after reaching `max_steps` depth.
/// Returns Vec<(u64, BigUint)> where u64 is the step at which the value was found.
/// If any target in `targets` is found, terminates early.
/// Seeds the queue with all initial values in `initials`.
/// Uses parallel processing within each BFS level.
pub fn collect_seen_values(
    tm: &TuringMachine,
    initials: &[BigUint],
    max_steps: u64,
    targets: &[BigUint],
    terminate_on_cycle: bool,
) -> (Vec<(u64, BigUint)>, Vec<usize>, bool) {
    use std::sync::atomic::{AtomicBool, Ordering};
    use parking_lot::Mutex;
    
    // Seed with all initial states
    let mut current_level: Vec<TMState> = initials.iter().map(|initial| {
        TMState {
            head_state: 1,
            head_position: 0,
            tape: Tape::from_integer(initial),
        }
    }).collect();
    
    // Build target set for fast lookup
    let target_set: HashSet<&BigUint> = targets.iter().collect();
    
    // Shared state protected by mutex
    let expanded: Mutex<HashMap<TMState, u64>> = Mutex::new(HashMap::new());
    let seen_set: Mutex<HashSet<(u64, BigUint)>> = Mutex::new(HashSet::new());
    let seen_order: Mutex<Vec<(u64, BigUint)>> = Mutex::new(Vec::new());
    
    let found_target = AtomicBool::new(false);
    let cycle_detected = AtomicBool::new(false);
    
    let mut queue_sizes: Vec<usize> = Vec::new();
    queue_sizes.push(current_level.len());
    
    let mut depth: u64 = 0;
    
    while !current_level.is_empty() && depth < max_steps {
        if aborted_safe() || found_target.load(Ordering::Relaxed) {
            break;
        }
        if terminate_on_cycle && cycle_detected.load(Ordering::Relaxed) {
            break;
        }
        
        // Process current level in parallel, collect next level states
        let next_level: Vec<TMState> = current_level
            .par_iter()
            .flat_map(|current_state| {
                let mut local_next: Vec<TMState> = Vec::new();
                
                // Check if already expanded
                {
                    let mut exp = expanded.lock();
                    if let Some(prev_depth) = exp.get(current_state) {
                        if depth > *prev_depth {
                            cycle_detected.store(true, Ordering::Relaxed);
                        }
                        return local_next; // already expanded
                    }
                    exp.insert(current_state.clone(), depth);
                }
                
                // Expand this state
                for (new_state, _rule_num, halted) in tm.ndtm_step(current_state) {
                    if halted {
                        let val = new_state.tape.to_integer();
                        let pair = (depth + 1, val.clone());
                        {
                            let mut ss = seen_set.lock();
                            if !ss.contains(&pair) {
                                ss.insert(pair.clone());
                                seen_order.lock().push(pair);
                            }
                        }
                        if target_set.contains(&val) {
                            found_target.store(true, Ordering::Relaxed);
                        }
                    } else {
                        local_next.push(new_state);
                    }
                }
                local_next
            })
            .collect();
        
        queue_sizes.push(next_level.len());
        current_level = next_level;
        depth += 1;
    }
    
    let final_seen = seen_order.into_inner();
    let final_cycle = cycle_detected.load(Ordering::Relaxed);
    (final_seen, queue_sizes, final_cycle)
}

/// Detect if the non-deterministic TM enters a cycle within max_steps.
/// Returns true if a cycle is detected, false otherwise.
/// Seeds the queue with all initial values in `initials`.
pub fn detect_cycle(
    tm: &TuringMachine,
    initials: &[BigUint],
    max_steps: u64,
) -> bool {
    let mut queue: VecDeque<(TMState, u64)> = VecDeque::new();
    // Seed queue with all initial states
    for initial in initials {
        let initial_tape = Tape::from_integer(initial);
        let initial_state = TMState {
            head_state: 1,
            head_position: 0,
            tape: initial_tape,
        };
        queue.push_back((initial_state, 0));
    }
    // Track insertion depth of each expanded state
    let mut expanded: HashMap<TMState, u64> = HashMap::new();
    
    while let Some((current_state, depth)) = queue.pop_front() {
        if aborted_safe() || depth >= max_steps { break; }
        
        if let Some(prev_depth) = expanded.get(&current_state) {
            // Cycle if we encounter same state at a greater depth
            if depth > *prev_depth {
                return true;
            }
            continue; 
        } else {
            expanded.insert(current_state.clone(), depth);
        }
        
        for (new_state, _rule_num, halted) in tm.ndtm_step(&current_state) {
            if !halted {
                queue.push_back((new_state, depth + 1));
            }
        }
    }
    false
}


/// Simple breadth traversal without collecting halted values; returns remaining queue size (0 => exhaustive termination)
/// Seeds the queue with all initial values in `initials`.
pub fn ndtm_traverse_queue_size(
    tm: &TuringMachine,
    initials: &[BigUint],
    max_steps: u64,
) -> usize {
    let mut queue: VecDeque<(TMState, u64)> = VecDeque::new();
    // Seed queue with all initial states
    for initial in initials {
        let initial_tape = Tape::from_integer(initial);
        let initial_state = TMState { head_state: 1, head_position: 0, tape: initial_tape };
        queue.push_back((initial_state, 0));
    }
    let mut expanded: HashSet<TMState> = HashSet::new();
    while let Some((current_state, depth)) = queue.pop_front() {
        if aborted_safe() || depth >= max_steps { break; }
        if expanded.contains(&current_state) { continue; }
        expanded.insert(current_state.clone());
        for (new_state, _rule_num, halted) in tm.ndtm_step(&current_state) {
            if !halted {
                queue.push_back((new_state, depth + 1));
            }
        }
    }
    queue.len()
}


/// Check if a single rule matches a target
fn rule_matches(tm: &TuringMachine, input: &BigUint, max_steps: u64, expected: &BigUint) -> bool {
    match run_dtm(tm, input, max_steps) {
        Some((_, val, _)) => val == *expected,
        None => false,
    }
}

/// Count how many targets a rule fails on. Returns early if errors exceed max_errors.
fn count_errors(tm: &TuringMachine, targets: &[(BigUint, u64, BigUint)], max_errors: u32) -> u32 {
    let mut errors = 0u32;
    for (input, max_steps, expected) in targets {
        if !rule_matches(tm, input, *max_steps, expected) {
            errors += 1;
            if errors > max_errors {
                return errors;
            }
        }
    }
    errors
}

/// Shared sieve: filter a Vec of candidate rule numbers against targets.
/// When min_errors == 0 && max_errors == 0, uses fast sequential pruning.
/// Otherwise, evaluates all targets per rule and checks min_errors <= errors <= max_errors.
fn sieve_candidates(
    num_states: u32,
    num_symbols: u32,
    mut candidates: Vec<u64>,
    targets: &[(BigUint, u64, BigUint)],
    min_errors: u32,
    max_errors: u32,
) -> Vec<u64> {
    if min_errors == 0 && max_errors == 0 {
        // Fast path: sequential sieve, prune after each target
        for (input, max_steps, expected_value) in targets {
            if candidates.is_empty() || aborted_safe() {
                break;
            }
            candidates = candidates
                .par_iter()
                .filter(|&&rule_num| {
                    if aborted_safe() { return false; }
                    let rule_bigint = BigInt::from(rule_num);
                    let tm = match TuringMachine::from_number(&rule_bigint, num_states, num_symbols) {
                        Ok(t) => t,
                        Err(_) => return false,
                    };
                    rule_matches(&tm, input, *max_steps, expected_value)
                })
                .copied()
                .collect();
        }
        candidates
    } else {
        // Approximate path: evaluate all targets per rule, count mismatches
        candidates
            .par_iter()
            .filter(|&&rule_num| {
                if aborted_safe() { return false; }
                let rule_bigint = BigInt::from(rule_num);
                let tm = match TuringMachine::from_number(&rule_bigint, num_states, num_symbols) {
                    Ok(t) => t,
                    Err(_) => return false,
                };
                let e = count_errors(&tm, targets, max_errors);
                e >= min_errors && e <= max_errors
            })
            .copied()
            .collect()
    }
}

/// Find all rule numbers in [min_rule, max_rule] matching targets
/// with min_errors <= mismatches <= max_errors.
pub fn find_matching_rules_range(
    num_states: u32,
    num_symbols: u32,
    min_rule: u64,
    max_rule: u64,
    targets: &[(BigUint, u64, BigUint)],
    min_errors: u32,
    max_errors: u32,
) -> Vec<u64> {
    if targets.is_empty() || min_rule > max_rule {
        return Vec::new();
    }

    if min_errors == 0 && max_errors == 0 {
        // Fast path: first iteration on range, then sieve
        let (input, max_steps, expected_value) = &targets[0];
        let candidates: Vec<u64> = (min_rule..=max_rule)
            .into_par_iter()
            .filter(|&rule_num| {
                if aborted_safe() { return false; }
                let rule_bigint = BigInt::from(rule_num);
                let tm = match TuringMachine::from_number(&rule_bigint, num_states, num_symbols) {
                    Ok(t) => t,
                    Err(_) => return false,
                };
                rule_matches(&tm, input, *max_steps, expected_value)
            })
            .collect();
        sieve_candidates(num_states, num_symbols, candidates, &targets[1..], 0, 0)
    } else {
        // Approximate path: evaluate all targets per rule
        (min_rule..=max_rule)
            .into_par_iter()
            .filter(|&rule_num| {
                if aborted_safe() { return false; }
                let rule_bigint = BigInt::from(rule_num);
                let tm = match TuringMachine::from_number(&rule_bigint, num_states, num_symbols) {
                    Ok(t) => t,
                    Err(_) => return false,
                };
                let e = count_errors(&tm, targets, max_errors);
                e >= min_errors && e <= max_errors
            })
            .collect()
    }
}

/// Find all rule numbers from an explicit list matching targets
/// with min_errors <= mismatches <= max_errors.
pub fn find_matching_rules_vec(
    num_states: u32,
    num_symbols: u32,
    rules: &[u64],
    targets: &[(BigUint, u64, BigUint)],
    min_errors: u32,
    max_errors: u32,
) -> Vec<u64> {
    if targets.is_empty() || rules.is_empty() {
        return Vec::new();
    }
    sieve_candidates(num_states, num_symbols, rules.to_vec(), targets, min_errors, max_errors)
}


// Wolfram LibraryLink wrappers
//
// The exported functions use `#[export(wxf)]` from wolfram-export: arguments
// arrive as one WXF payload (the kernel-side loader generated by
// `cargo wl build` serializes the argument list with BinarySerialize) and the
// return value goes back the same way. Boundary conventions:
//
//   - Rule numbers and tape values are arbitrary-precision, so list-shaped
//     arguments cross as `Expr` (a WL list arrives as either a `List` normal
//     of Integer/BigInteger leaves or, when the kernel packs it, an i64
//     PackedArray) and are decoded by the `expr_*` helpers below.
//   - Scalar counts/limits cross as `i64` and are narrowed here.
//   - Structured results are built as `Expr` trees: tables keep the historical
//     shape (cells are the value, `{steps, value, ...}`, or the bare symbol
//     `None` for non-halting), so the WL side reads exactly what the old
//     custom-WXF encoding produced.
//   - Dense numeric tables return `wolfram_expr::NumericArray` (u64 / f64),
//     which BinaryDeserializes back into a NumericArray on the WL side.

use wolfram_export::export;
use wolfram_expr::{BigInteger, Expr, ExprKind, NumericArray, Symbol};

// ---- Expr boundary helpers ----

fn expr_int(e: &Expr) -> Option<BigInt> {
    match e.kind() {
        ExprKind::Integer(i) => Some(BigInt::from(*i)),
        ExprKind::BigInteger(b) => b.as_str().parse::<BigInt>().ok(),
        _ => None,
    }
}

/// Widen a packed integer array of any element width to i64s. WXF writes the
/// narrowest width that fits (Range[8] arrives as Integer8), so every integer
/// element type must be accepted.
fn packed_i64s(pa: &wolfram_expr::PackedArray) -> Option<Vec<i64>> {
    if let Some(s) = pa.try_as_slice::<i64>() {
        return Some(s.to_vec());
    }
    if let Some(s) = pa.try_as_slice::<i32>() {
        return Some(s.iter().map(|&v| v as i64).collect());
    }
    if let Some(s) = pa.try_as_slice::<i16>() {
        return Some(s.iter().map(|&v| v as i64).collect());
    }
    if let Some(s) = pa.try_as_slice::<i8>() {
        return Some(s.iter().map(|&v| v as i64).collect());
    }
    None
}

fn numeric_i64s(na: &NumericArray) -> Option<Vec<i64>> {
    if let Some(s) = na.try_as_slice::<i64>() {
        return Some(s.to_vec());
    }
    if let Some(s) = na.try_as_slice::<u64>() {
        return Some(s.iter().map(|&v| v as i64).collect());
    }
    if let Some(s) = na.try_as_slice::<i32>() {
        return Some(s.iter().map(|&v| v as i64).collect());
    }
    if let Some(s) = na.try_as_slice::<u32>() {
        return Some(s.iter().map(|&v| v as i64).collect());
    }
    if let Some(s) = na.try_as_slice::<i16>() {
        return Some(s.iter().map(|&v| v as i64).collect());
    }
    if let Some(s) = na.try_as_slice::<u16>() {
        return Some(s.iter().map(|&v| v as i64).collect());
    }
    if let Some(s) = na.try_as_slice::<i8>() {
        return Some(s.iter().map(|&v| v as i64).collect());
    }
    if let Some(s) = na.try_as_slice::<u8>() {
        return Some(s.iter().map(|&v| v as i64).collect());
    }
    None
}

/// Integers of a WL list: a `List` normal of Integer/BigInteger leaves, or a
/// packed / numeric array of machine integers.
fn expr_ints(e: &Expr) -> Vec<BigInt> {
    match e.kind() {
        ExprKind::Normal(n) => n.elements().iter().filter_map(expr_int).collect(),
        ExprKind::PackedArray(pa) => packed_i64s(pa)
            .map(|s| s.into_iter().map(BigInt::from).collect())
            .unwrap_or_default(),
        ExprKind::NumericArray(na) => numeric_i64s(na)
            .map(|s| s.into_iter().map(BigInt::from).collect())
            .unwrap_or_default(),
        _ => Vec::new(),
    }
}

fn expr_biguints(e: &Expr) -> Vec<BigUint> {
    expr_ints(e).into_iter().filter_map(|i| i.to_biguint()).collect()
}

fn expr_u64s(e: &Expr) -> Vec<u64> {
    expr_ints(e).into_iter().filter_map(|i| i.to_u64()).collect()
}

/// Rows of a rectangular WL integer matrix: a rank-2 i64 PackedArray or a
/// `List` normal of integer-list rows.
fn expr_int_rows(e: &Expr) -> Vec<Vec<i64>> {
    match e.kind() {
        ExprKind::PackedArray(pa) => {
            let dims = pa.dimensions().to_vec();
            if dims.len() == 2 && dims[1] > 0 {
                if let Some(s) = packed_i64s(pa) {
                    return s.chunks(dims[1]).map(|c| c.to_vec()).collect();
                }
            }
            Vec::new()
        },
        ExprKind::Normal(n) => n
            .elements()
            .iter()
            .map(|row| expr_ints(row).into_iter().filter_map(|i| i.to_i64()).collect())
            .collect(),
        _ => Vec::new(),
    }
}

fn expr_triples(e: &Expr) -> Vec<(u32, u32, i32)> {
    expr_int_rows(e)
        .into_iter()
        .filter(|r| r.len() == 3)
        .map(|r| (r[0] as u32, r[1] as u32, r[2] as i32))
        .collect()
}

fn expr_quints(e: &Expr) -> Vec<(u32, u32, u32, u32, i32)> {
    expr_int_rows(e)
        .into_iter()
        .filter(|r| r.len() == 5)
        .map(|r| (r[0] as u32, r[1] as u32, r[2] as u32, r[3] as u32, r[4] as i32))
        .collect()
}

/// WL booleans arrive as the bare symbol `True`/`False` (BinarySerialize
/// omits the System` context), which the published FromWXF-for-bool rejects,
/// so boolean flags cross as `Expr` and are read here.
fn expr_bool(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Symbol(s) if s.as_str() == "True" || s.as_str() == "System`True")
}

fn none_expr() -> Expr {
    Expr::symbol(Symbol::new("System`None"))
}

fn bigint_expr(v: &BigInt) -> Expr {
    match v.to_i64() {
        Some(i) => Expr::from(i),
        None => Expr::from(BigInteger(v.to_string())),
    }
}

fn biguint_expr(v: &BigUint) -> Expr {
    match v.to_i64() {
        Some(i) => Expr::from(i),
        None => Expr::from(BigInteger(v.to_string())),
    }
}

fn value_table_expr(table: Vec<Vec<Option<BigUint>>>) -> Expr {
    Expr::list(
        table
            .into_iter()
            .map(|row| {
                Expr::list(
                    row.into_iter()
                        .map(|cell| match cell {
                            Some(v) => biguint_expr(&v),
                            None => none_expr(),
                        })
                        .collect(),
                )
            })
            .collect(),
    )
}

fn steps_value_table_expr(table: Vec<Vec<Option<(u64, BigUint)>>>) -> Expr {
    Expr::list(
        table
            .into_iter()
            .map(|row| {
                Expr::list(
                    row.into_iter()
                        .map(|cell| match cell {
                            Some((steps, v)) => {
                                Expr::list(vec![Expr::from(steps as i64), biguint_expr(&v)])
                            },
                            None => none_expr(),
                        })
                        .collect(),
                )
            })
            .collect(),
    )
}

fn triple_table_expr(table: Vec<Vec<Option<(u64, BigUint, u64)>>>) -> Expr {
    Expr::list(
        table
            .into_iter()
            .map(|row| {
                Expr::list(
                    row.into_iter()
                        .map(|cell| match cell {
                            Some((steps, v, width)) => Expr::list(vec![
                                Expr::from(steps as i64),
                                biguint_expr(&v),
                                Expr::from(width as i64),
                            ]),
                            None => none_expr(),
                        })
                        .collect(),
                )
            })
            .collect(),
    )
}

fn history_table_expr(table: Vec<Vec<Vec<(u32, usize, BigUint)>>>) -> Expr {
    Expr::list(
        table
            .into_iter()
            .map(|row| {
                Expr::list(
                    row.into_iter()
                        .map(|history| {
                            Expr::list(
                                history
                                    .into_iter()
                                    .map(|(state, pos, v)| {
                                        Expr::list(vec![
                                            Expr::from(state as i64),
                                            Expr::from(pos as i64),
                                            biguint_expr(&v),
                                        ])
                                    })
                                    .collect(),
                            )
                        })
                        .collect(),
                )
            })
            .collect(),
    )
}

/// `{ {{step, value}..}, {queueSize..}, cycleDetected }` — the shape all four
/// collect_seen_values variants return.
fn seen_values_expr(vals: Vec<(u64, BigUint)>, queues: Vec<usize>, cycle: bool) -> Expr {
    Expr::list(vec![
        Expr::list(
            vals.into_iter()
                .map(|(step, v)| Expr::list(vec![Expr::from(step as i64), biguint_expr(&v)]))
                .collect(),
        ),
        Expr::list(queues.into_iter().map(|q| Expr::from(q as i64)).collect()),
        Expr::from(cycle),
    ])
}

// ---- exported functions ----

#[export(wxf)]
fn exhaustive_search_wl(
    rules: Expr,
    num_states: i64,
    num_symbols: i64,
    initials: Expr,
    targets: Expr,
    max_steps: i64,
) -> Expr {
    let rule_bigints = expr_ints(&rules);
    let tm =
        TuringMachine::from_numbers(&rule_bigints, num_states as u32, num_symbols as u32).unwrap();
    let initial_biguints = expr_biguints(&initials);
    let target_biguints = expr_biguints(&targets);
    let path = exhaustive_search_seq(&tm, &initial_biguints, &target_biguints, max_steps as u64)
        .unwrap_or_default();
    Expr::list(
        path.into_iter()
            .map(|idx| match rule_bigints.get(idx as usize) {
                Some(rule) => bigint_expr(rule),
                None => Expr::from(idx as i64),
            })
            .collect(),
    )
}

#[export(wxf)]
fn exhaustive_search_parallel_wl(
    rules: Expr,
    num_states: i64,
    num_symbols: i64,
    initials: Expr,
    targets: Expr,
    max_steps: i64,
) -> Expr {
    let rule_bigints = expr_ints(&rules);
    let tm =
        TuringMachine::from_numbers(&rule_bigints, num_states as u32, num_symbols as u32).unwrap();
    let initial_biguints = expr_biguints(&initials);
    let target_biguints = expr_biguints(&targets);
    let path =
        exhaustive_search_parallel(&tm, &initial_biguints, &target_biguints, max_steps as u64)
            .unwrap_or_default();
    Expr::list(
        path.into_iter()
            .map(|idx| match rule_bigints.get(idx as usize) {
                Some(rule) => bigint_expr(rule),
                None => Expr::from(idx as i64),
            })
            .collect(),
    )
}

#[export(wxf)]
fn run_dtm_wl(
    rule_triples: Expr,
    num_states: i64,
    num_symbols: i64,
    initial: Expr,
    max_steps: i64,
) -> Expr {
    let failed = || Expr::list(vec![Expr::from(0), Expr::from(0), Expr::from(0)]);
    let rule_triples = expr_triples(&rule_triples);
    let tm = match TuringMachine::from_rule_triples(&rule_triples, num_states as u32, num_symbols as u32)
    {
        Ok(t) => t,
        Err(_) => return failed(),
    };
    let initial_biguint = match expr_int(&initial).and_then(|i| i.to_biguint()) {
        Some(v) => v,
        None => return failed(),
    };
    match run_dtm(&tm, &initial_biguint, max_steps as u64) {
        Some((steps, out, pos)) => Expr::list(vec![
            Expr::from(steps as i64),
            biguint_expr(&out),
            Expr::from((pos + 1) as i64),
        ]),
        None => failed(),
    }
}

#[export(wxf)]
fn run_dtm_with_history_wl(
    rule_triples: Expr,
    num_states: i64,
    num_symbols: i64,
    initial: Expr,
    max_steps: i64,
) -> Expr {
    let rule_triples = expr_triples(&rule_triples);
    let tm = match TuringMachine::from_rule_triples(&rule_triples, num_states as u32, num_symbols as u32)
    {
        Ok(t) => t,
        Err(_) => return Expr::list(Vec::new()),
    };
    let initial_biguint = match expr_int(&initial).and_then(|i| i.to_biguint()) {
        Some(v) => v,
        None => return Expr::list(Vec::new()),
    };
    let history = run_dtm_with_history(&tm, &initial_biguint, max_steps as u64);
    Expr::list(
        history
            .into_iter()
            .map(|(state, pos, value)| {
                Expr::list(vec![
                    Expr::from(state as i64),
                    Expr::from(pos as i64),
                    biguint_expr(&value),
                ])
            })
            .collect(),
    )
}

#[export(wxf)]
fn collect_seen_values_wl(
    rules: Expr,
    num_states: i64,
    num_symbols: i64,
    initials: Expr,
    targets: Expr,
    max_steps: i64,
    terminate_on_cycle: Expr,
) -> Expr {
    let rule_bigints = expr_ints(&rules);
    let tm =
        TuringMachine::from_numbers(&rule_bigints, num_states as u32, num_symbols as u32).unwrap();
    let initial_biguints = expr_biguints(&initials);
    let target_biguints = expr_biguints(&targets);
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(
        &tm,
        &initial_biguints,
        max_steps as u64,
        &target_biguints,
        expr_bool(&terminate_on_cycle),
    );
    seen_values_expr(vals, queue_sizes, cycle_detected)
}

#[export(wxf)]
fn detect_cycle_wl(
    rules: Expr,
    num_states: i64,
    num_symbols: i64,
    initials: Expr,
    max_steps: i64,
) -> bool {
    let rule_bigints = expr_ints(&rules);
    let tm =
        TuringMachine::from_numbers(&rule_bigints, num_states as u32, num_symbols as u32).unwrap();
    let initial_biguints = expr_biguints(&initials);
    detect_cycle(&tm, &initial_biguints, max_steps as u64)
}

#[export(wxf)]
fn ndtm_traverse_queue_size_wl(
    rules: Expr,
    num_states: i64,
    num_symbols: i64,
    initials: Expr,
    max_steps: i64,
) -> i64 {
    let rule_bigints = expr_ints(&rules);
    let tm =
        TuringMachine::from_numbers(&rule_bigints, num_states as u32, num_symbols as u32).unwrap();
    let initial_biguints = expr_biguints(&initials);
    ndtm_traverse_queue_size(&tm, &initial_biguints, max_steps as u64) as i64
}

/// Deterministic TM rules as `{{{state, symbol}, {nextState, write, dir}}..}`;
/// direction: +1 for right, -1 for left.
#[export(wxf)]
fn tm_rules_from_number_wl(rule_number: Expr, num_states: i64, num_symbols: i64) -> Expr {
    let num_states = num_states as u32;
    let num_symbols = num_symbols as u32;
    let n = expr_int(&rule_number).unwrap();
    let tm = TuringMachine::from_number(&n, num_states, num_symbols).unwrap();
    let mut out: Vec<Expr> = Vec::with_capacity((num_states * num_symbols) as usize);
    for state in 1..=num_states {
        for symbol in 0..num_symbols {
            if let Some(rule) = tm.get_rule(state, symbol) {
                out.push(Expr::list(vec![
                    Expr::list(vec![Expr::from(state as i64), Expr::from(symbol as i64)]),
                    Expr::list(vec![
                        Expr::from(rule.next_state as i64),
                        Expr::from(rule.write_symbol as i64),
                        Expr::from(if rule.move_right { 1 } else { -1 }),
                    ]),
                ]));
            }
        }
    }
    Expr::list(out)
}

/// Non-deterministic TM rules as `{{{state, symbol}, {{next, write, dir}..}}..}`.
#[export(wxf)]
fn tm_rules_from_numbers_wl(rule_numbers: Expr, num_states: i64, num_symbols: i64) -> Expr {
    let num_states = num_states as u32;
    let num_symbols = num_symbols as u32;
    let nums = expr_ints(&rule_numbers);
    let tm = TuringMachine::from_numbers(&nums, num_states, num_symbols).unwrap();
    let mut out: Vec<Expr> = Vec::with_capacity((num_states * num_symbols) as usize);
    for state in 1..=num_states {
        for symbol in 0..num_symbols {
            let rules = tm.get_rules(state, symbol);
            let some_rules: Vec<Rule> = rules.into_iter().flatten().collect();
            if !some_rules.is_empty() {
                let variants: Vec<Expr> = some_rules
                    .into_iter()
                    .map(|r| {
                        Expr::list(vec![
                            Expr::from(r.next_state as i64),
                            Expr::from(r.write_symbol as i64),
                            Expr::from(if r.move_right { 1 } else { -1 }),
                        ])
                    })
                    .collect();
                out.push(Expr::list(vec![
                    Expr::list(vec![Expr::from(state as i64), Expr::from(symbol as i64)]),
                    Expr::list(variants),
                ]));
            }
        }
    }
    Expr::list(out)
}

#[export(wxf)]
fn dtm_output_table_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> Expr {
    value_table_expr(dtm_output_table(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    ))
}

#[export(wxf)]
fn dtm_output_table_parallel_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> Expr {
    value_table_expr(dtm_output_table_parallel(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    ))
}

#[export(wxf)]
fn dtm_output_table_triple_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> Expr {
    triple_table_expr(dtm_output_table_triple(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    ))
}

#[export(wxf)]
fn dtm_output_table_triple_parallel_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> Expr {
    triple_table_expr(dtm_output_table_triple_parallel(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    ))
}

#[export(wxf)]
fn dtm_output_table_triple_with_history_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> Expr {
    history_table_expr(dtm_output_table_triple_with_history(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    ))
}

#[export(wxf)]
fn dtm_output_table_triple_with_history_parallel_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> Expr {
    history_table_expr(dtm_output_table_triple_with_history_parallel(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    ))
}

/// Contiguous f64 (step, value) pairs; {0.0, 0.0} for non-halting cases.
/// Dimensions: [num_rules, num_inputs, 2].
#[export(wxf)]
fn dtm_output_table_pair_parallel_f64_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> NumericArray {
    let arr = dtm_output_table_pair_parallel_f64(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    );
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    NumericArray::from_slice(vec![num_rules, num_inputs, 2], &arr)
}

/// 2D u64 step counts (0 for non-halting). Dimensions: [num_rules, num_inputs].
#[export(wxf)]
fn dtm_output_table_parallel_steps_u64_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> NumericArray {
    let arr = dtm_output_table_parallel_steps_u64(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    );
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    NumericArray::from_slice(vec![num_rules, num_inputs], &arr)
}

/// 2D u64 max widths (0 for non-halting). Dimensions: [num_rules, num_inputs].
#[export(wxf)]
fn dtm_output_table_parallel_width_u64_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> NumericArray {
    let arr = dtm_output_table_parallel_width_u64(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    );
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    NumericArray::from_slice(vec![num_rules, num_inputs], &arr)
}

#[export(wxf)]
fn dtm_output_table_parallel_steps_width_u64_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> NumericArray {
    let arr = dtm_output_table_parallel_steps_width_u64(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    );
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    NumericArray::from_slice(vec![num_rules, num_inputs, 2], &arr)
}

/// (steps, value) pairs with full precision.
#[export(wxf)]
fn dtm_output_table_parallel_steps_value_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> Expr {
    steps_value_table_expr(dtm_output_table_parallel_steps_value(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    ))
}

/// 3D f64 triples (steps, value, width); non-halting has {0.0, 0.0, 0.0}.
#[export(wxf)]
fn dtm_output_table_triple_parallel_f64_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    min_rule: i64,
    max_rule: i64,
    min_input: i64,
    max_input: i64,
) -> NumericArray {
    let arr = dtm_output_table_triple_parallel_f64(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        min_rule as u64,
        max_rule as u64,
        min_input as u32,
        max_input as u32,
    );
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    NumericArray::from_slice(vec![num_rules, num_inputs, 3], &arr)
}

// =============================================================================
// Vec-based WL export wrappers (explicit rule / input lists)
// =============================================================================

#[export(wxf)]
fn dtm_output_table_parallel_vec_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    rules: Expr,
    inputs: Expr,
) -> Expr {
    let rules_big = expr_ints(&rules);
    let inputs_big = expr_biguints(&inputs);
    value_table_expr(dtm_output_table_parallel_vec(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        &rules_big,
        &inputs_big,
    ))
}

#[export(wxf)]
fn dtm_output_table_triple_parallel_vec_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    rules: Expr,
    inputs: Expr,
) -> Expr {
    let rules_big = expr_ints(&rules);
    let inputs_big = expr_biguints(&inputs);
    triple_table_expr(dtm_output_table_triple_parallel_vec(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        &rules_big,
        &inputs_big,
    ))
}

#[export(wxf)]
fn dtm_output_table_parallel_steps_u64_vec_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    rules: Expr,
    inputs: Expr,
) -> NumericArray {
    let rules_big = expr_ints(&rules);
    let inputs_big = expr_biguints(&inputs);
    let arr = dtm_output_table_parallel_steps_u64_vec(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        &rules_big,
        &inputs_big,
    );
    NumericArray::from_slice(vec![rules_big.len(), inputs_big.len()], &arr)
}

#[export(wxf)]
fn dtm_output_table_parallel_width_u64_vec_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    rules: Expr,
    inputs: Expr,
) -> NumericArray {
    let rules_big = expr_ints(&rules);
    let inputs_big = expr_biguints(&inputs);
    let arr = dtm_output_table_parallel_width_u64_vec(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        &rules_big,
        &inputs_big,
    );
    NumericArray::from_slice(vec![rules_big.len(), inputs_big.len()], &arr)
}

#[export(wxf)]
fn dtm_output_table_parallel_steps_width_u64_vec_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    rules: Expr,
    inputs: Expr,
) -> NumericArray {
    let rules_big = expr_ints(&rules);
    let inputs_big = expr_biguints(&inputs);
    let arr = dtm_output_table_parallel_steps_width_u64_vec(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        &rules_big,
        &inputs_big,
    );
    NumericArray::from_slice(vec![rules_big.len(), inputs_big.len() * 2], &arr)
}

#[export(wxf)]
fn dtm_output_table_pair_parallel_f64_vec_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    rules: Expr,
    inputs: Expr,
) -> NumericArray {
    let rules_big = expr_ints(&rules);
    let inputs_big = expr_biguints(&inputs);
    let arr = dtm_output_table_pair_parallel_f64_vec(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        &rules_big,
        &inputs_big,
    );
    NumericArray::from_slice(vec![rules_big.len(), inputs_big.len() * 2], &arr)
}

#[export(wxf)]
fn dtm_output_table_parallel_steps_value_vec_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    rules: Expr,
    inputs: Expr,
) -> Expr {
    let rules_big = expr_ints(&rules);
    let inputs_big = expr_biguints(&inputs);
    steps_value_table_expr(dtm_output_table_parallel_steps_value_vec(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        &rules_big,
        &inputs_big,
    ))
}

#[export(wxf)]
fn dtm_output_table_triple_parallel_f64_vec_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    rules: Expr,
    inputs: Expr,
) -> NumericArray {
    let rules_big = expr_ints(&rules);
    let inputs_big = expr_biguints(&inputs);
    let arr = dtm_output_table_triple_parallel_f64_vec(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        &rules_big,
        &inputs_big,
    );
    NumericArray::from_slice(vec![rules_big.len(), inputs_big.len() * 3], &arr)
}

#[export(wxf)]
fn dtm_output_table_triple_with_history_parallel_vec_wl(
    num_states: i64,
    num_symbols: i64,
    max_steps: i64,
    rules: Expr,
    inputs: Expr,
) -> Expr {
    let rules_big = expr_ints(&rules);
    let inputs_big = expr_biguints(&inputs);
    history_table_expr(dtm_output_table_triple_with_history_parallel_vec(
        num_states as u32,
        num_symbols as u32,
        max_steps as u64,
        &rules_big,
        &inputs_big,
    ))
}

#[export(wxf)]
fn collect_seen_values_tuples_wl(
    rules: Expr,
    num_states: i64,
    num_symbols: i64,
    initials: Expr,
    targets: Expr,
    max_steps: i64,
    terminate_on_cycle: Expr,
) -> Expr {
    let rules = expr_quints(&rules);
    let tm = match TuringMachine::from_rule_tuples(&rules, num_states as u32, num_symbols as u32) {
        Ok(t) => t,
        Err(_) => return seen_values_expr(Vec::new(), Vec::new(), false),
    };
    let initial_biguints = expr_biguints(&initials);
    let target_biguints = expr_biguints(&targets);
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(
        &tm,
        &initial_biguints,
        max_steps as u64,
        &target_biguints,
        expr_bool(&terminate_on_cycle),
    );
    seen_values_expr(vals, queue_sizes, cycle_detected)
}

#[export(wxf)]
fn collect_seen_values_triples_wl(
    rules: Expr,
    num_states: i64,
    num_symbols: i64,
    initials: Expr,
    targets: Expr,
    max_steps: i64,
    terminate_on_cycle: Expr,
) -> Expr {
    let rules = expr_triples(&rules);
    let tm = match TuringMachine::from_rule_triples(&rules, num_states as u32, num_symbols as u32) {
        Ok(t) => t,
        Err(_) => return seen_values_expr(Vec::new(), Vec::new(), false),
    };
    let initial_biguints = expr_biguints(&initials);
    let target_biguints = expr_biguints(&targets);
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(
        &tm,
        &initial_biguints,
        max_steps as u64,
        &target_biguints,
        expr_bool(&terminate_on_cycle),
    );
    seen_values_expr(vals, queue_sizes, cycle_detected)
}

#[export(wxf)]
fn collect_seen_values_tuples_inferred_wl(
    rules: Expr,
    initials: Expr,
    targets: Expr,
    max_steps: i64,
    terminate_on_cycle: Expr,
) -> Expr {
    let rules = expr_quints(&rules);
    let tm = match TuringMachine::from_rule_tuples_inferred(&rules) {
        Ok(t) => t,
        Err(_) => return seen_values_expr(Vec::new(), Vec::new(), false),
    };
    let initial_biguints = expr_biguints(&initials);
    let target_biguints = expr_biguints(&targets);
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(
        &tm,
        &initial_biguints,
        max_steps as u64,
        &target_biguints,
        expr_bool(&terminate_on_cycle),
    );
    seen_values_expr(vals, queue_sizes, cycle_detected)
}

/// Matching rule numbers over a contiguous rule range; targets given as three
/// parallel lists (inputs, per-input step limits, expected values).
#[export(wxf)]
fn find_matching_rules_range_wl(
    num_states: i64,
    num_symbols: i64,
    min_rule: i64,
    max_rule: i64,
    inputs: Expr,
    max_steps_vec: Expr,
    expected_values: Expr,
    min_errors: i64,
    max_errors: i64,
) -> Expr {
    let inputs = expr_biguints(&inputs);
    let max_steps_vec = expr_u64s(&max_steps_vec);
    let expected_values = expr_biguints(&expected_values);
    let targets: Vec<(BigUint, u64, BigUint)> = inputs
        .into_iter()
        .zip(max_steps_vec)
        .zip(expected_values)
        .map(|((inp, steps), exp)| (inp, steps, exp))
        .collect();
    Expr::list(
        find_matching_rules_range(
            num_states as u32,
            num_symbols as u32,
            min_rule as u64,
            max_rule as u64,
            &targets,
            min_errors as u32,
            max_errors as u32,
        )
        .into_iter()
        .map(|r| Expr::from(r as i64))
        .collect(),
    )
}

/// Matching rule numbers over an explicit rule list.
#[export(wxf)]
fn find_matching_rules_vec_wl(
    num_states: i64,
    num_symbols: i64,
    rules: Expr,
    inputs: Expr,
    max_steps_vec: Expr,
    expected_values: Expr,
    min_errors: i64,
    max_errors: i64,
) -> Expr {
    let rule_nums = expr_u64s(&rules);
    let inputs = expr_biguints(&inputs);
    let max_steps_vec = expr_u64s(&max_steps_vec);
    let expected_values = expr_biguints(&expected_values);
    let targets: Vec<(BigUint, u64, BigUint)> = inputs
        .into_iter()
        .zip(max_steps_vec)
        .zip(expected_values)
        .map(|((inp, steps), exp)| (inp, steps, exp))
        .collect();
    Expr::list(
        find_matching_rules_vec(
            num_states as u32,
            num_symbols as u32,
            &rule_nums,
            &targets,
            min_errors as u32,
            max_errors as u32,
        )
        .into_iter()
        .map(|r| Expr::from(r as i64))
        .collect(),
    )
}
