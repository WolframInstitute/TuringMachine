use num_traits::ToPrimitive;
use wolfram_library_link as wll;

wll::generate_loader!(rustlink_autodiscover);

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



// Wolfram LibraryLink wrappers

#[wll::export]
pub fn exhaustive_search_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initials: Vec<String>,
    targets: Vec<String>,
    max_steps: u64,
) -> Vec<String> {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguints: Vec<BigUint> = initials.iter().filter_map(|s| s.parse::<BigUint>().ok()).collect();
    let target_biguints: Vec<BigUint> = targets.iter().filter_map(|s| s.parse::<BigUint>().ok()).collect();
    match exhaustive_search_seq(&tm, &initial_biguints, &target_biguints, max_steps) {
        Some(path) => path
            .into_iter()
            .map(|idx| {
                // idx is origin_index into the original rules vector
                if (idx as usize) < rules.len() {
                    rules[idx as usize].clone()
                } else {
                    // Fallback: return index as string if out of bounds (should not happen)
                    idx.to_string()
                }
            })
            .collect(),
        None => Vec::new(),
    }
}

#[wll::export]
pub fn exhaustive_search_parallel_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initials: Vec<String>,
    targets: Vec<String>,
    max_steps: u64,
) -> Vec<String> {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguints: Vec<BigUint> = initials.iter().filter_map(|s| s.parse::<BigUint>().ok()).collect();
    let target_biguints: Vec<BigUint> = targets.iter().filter_map(|s| s.parse::<BigUint>().ok()).collect();
    match exhaustive_search_parallel(&tm, &initial_biguints, &target_biguints, max_steps) {
        Some(path) => path
            .into_iter()
            .map(|idx| {
                if (idx as usize) < rules.len() {
                    rules[idx as usize].clone()
                } else {
                    idx.to_string()
                }
            })
            .collect(),
        None => Vec::new(),
    }
}


#[wll::export]
pub fn run_dtm_wl(
    rule_triples: Vec<(u32, u32, i32)>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    max_steps: u64,
) -> (u64, String, u64) {
    let tm = match TuringMachine::from_rule_triples(&rule_triples, num_states, num_symbols) { Ok(t) => t, Err(_) => return (0, String::new(), 0) };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() { Ok(v) => v, Err(_) => return (0, String::new(), 0) };
    match run_dtm(&tm, &initial_biguint, max_steps) { Some((steps, out, pos)) => (steps, out.to_string(), pos + 1), None => (0, String::new(), 0) }
}

#[wll::export]
pub fn run_dtm_with_history_wl(
    rule_triples: Vec<(u32, u32, i32)>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    max_steps: u64,
) -> Vec<(u32, u64, String)> {
    let tm = match TuringMachine::from_rule_triples(&rule_triples, num_states, num_symbols) { 
        Ok(t) => t, 
        Err(_) => return Vec::new() 
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() { 
        Ok(v) => v, 
        Err(_) => return Vec::new() 
    };
    let history = run_dtm_with_history(&tm, &initial_biguint, max_steps);
    // Convert usize to u64 and BigUint to String for WL
    history.into_iter()
        .map(|(state, pos, value)| (state, pos as u64, value.to_string()))
        .collect()
}


#[wll::export]
pub fn collect_seen_values_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initials: Vec<String>,
    targets: Vec<String>,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguints: Vec<BigUint> = initials.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let target_biguints: Vec<BigUint> = targets.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguints, max_steps, &target_biguints, terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}

#[wll::export]
pub fn detect_cycle_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initials: Vec<String>,
    max_steps: u64,
) -> bool {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguints: Vec<BigUint> = initials.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    detect_cycle(&tm, &initial_biguints, max_steps)
}

#[wll::export]
pub fn ndtm_traverse_queue_size_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initials: Vec<String>,
    max_steps: u64,
) -> usize {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguints: Vec<BigUint> = initials.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    ndtm_traverse_queue_size(&tm, &initial_biguints, max_steps)
}

/// Export deterministic TM rules without strings or rule numbers.
/// Returns Vec of ((state, symbol), (next_state, write_symbol, direction)).
/// direction: +1 for right, -1 for left.
#[wll::export]
pub fn tm_rules_from_number_wl(
    rule_number: String,
    num_states: u32,
    num_symbols: u32,
) -> Vec<((u32, u32), (u32, u32, i32))> {
    let n: BigInt = rule_number.parse::<BigInt>().unwrap();
    let tm = TuringMachine::from_number(&n, num_states, num_symbols).unwrap();
    let mut out: Vec<((u32, u32), (u32, u32, i32))> = Vec::with_capacity((num_states * num_symbols) as usize);
    for state in 1..=num_states {
        for symbol in 0..num_symbols {
            if let Some(rule) = tm.get_rule(state, symbol) {
                out.push(((state, symbol), (rule.next_state, rule.write_symbol, if rule.move_right { 1 } else { -1 })));
            }
        }
    }
    out
}

/// Export non-deterministic TM rules from multiple rule numbers.
/// Returns Vec of ((state, symbol), Vec<(next_state, write_symbol, direction)>).
#[wll::export]
pub fn tm_rules_from_numbers_wl(
    rule_numbers: Vec<String>,
    num_states: u32,
    num_symbols: u32,
) -> Vec<((u32, u32), Vec<(u32, u32, i32)>)> {
    let nums: Vec<BigInt> = rule_numbers.into_iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&nums, num_states, num_symbols).unwrap();
    let mut out: Vec<((u32, u32), Vec<(u32, u32, i32)>)> = Vec::with_capacity((num_states * num_symbols) as usize);
    for state in 1..=num_states {
        for symbol in 0..num_symbols {
            let rules = tm.get_rules(state, symbol);
            let some_rules: Vec<Rule> = rules.into_iter().filter_map(|opt| opt).collect();
            if !some_rules.is_empty() {
                let mut variants: Vec<(u32, u32, i32)> = Vec::with_capacity(some_rules.len());
                for r in some_rules {
                    variants.push((r.next_state, r.write_symbol, if r.move_right { 1 } else { -1 }));
                }
                out.push(((state, symbol), variants));
            }
        }
    }
    out
}



/// Non-halting entries are empty strings.
#[wll::export]
pub fn dtm_output_table_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<u8> {
    let table = dtm_output_table(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table).unwrap())
}

/// Parallel WL wrapper (string conversion); non-halting entries empty string.
#[wll::export]
pub fn dtm_output_table_parallel_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<u8> {
    let table = dtm_output_table_parallel(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table).unwrap())
}

#[wll::export]
pub fn dtm_output_table_triple_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<u8> {
    let table = dtm_output_table_triple(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table).unwrap())
}


/// Parallel WL wrapper including step counts.
#[wll::export]
pub fn dtm_output_table_triple_parallel_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<u8> {
    let table = dtm_output_table_triple_parallel(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table).unwrap())
}

/// WL wrapper for dtm_output_table_triple_with_history (sequential version).
#[wll::export]
pub fn dtm_output_table_triple_with_history_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<u8> {
    let table = dtm_output_table_triple_with_history(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    // Convert usize to u64 for WXF serialization
    let table_u64: Vec<Vec<Vec<(u32, u64, BigUint)>>> = table
        .into_iter()
        .map(|row| row.into_iter().map(|history| history.into_iter().map(|(s, p, v)| (s, p as u64, v)).collect()).collect())
        .collect();
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table_u64).unwrap())
}

/// WL wrapper for dtm_output_table_triple_with_history_parallel (parallel version).
#[wll::export]
pub fn dtm_output_table_triple_with_history_parallel_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<u8> {
    let table = dtm_output_table_triple_with_history_parallel(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    // Convert usize to u64 for WXF serialization
    let table_u64: Vec<Vec<Vec<(u32, u64, BigUint)>>> = table
        .into_iter()
        .map(|row| row.into_iter().map(|history| history.into_iter().map(|(s, p, v)| (s, p as u64, v)).collect()).collect())
        .collect();
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table_u64).unwrap())
}

/// Parallel WL wrapper returning contiguous array of f64 pairs (step, value), {0.0, 0.0} for non-halting cases.
#[wll::export]
pub fn dtm_output_table_pair_parallel_f64_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<f64> {
    let arr = dtm_output_table_pair_parallel_f64(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    // Dimensions: [num_rules, num_inputs, 2] where last index 0 = steps, 1 = value
    wll::NumericArray::from_array(&[num_rules, num_inputs, 2], &arr)
}

/// WL wrapper returning a 2D NumericArray<u64> of steps (0 for non-halting). Dimensions: [num_rules, num_inputs]
#[wll::export]
pub fn dtm_output_table_parallel_steps_u64_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<u64> {
    let arr = dtm_output_table_parallel_steps_u64(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    wll::NumericArray::from_array(&[num_rules, num_inputs], &arr)
}

/// WL wrapper returning a 2D NumericArray<u64> of max widths (0 for non-halting). Dimensions: [num_rules, num_inputs]
#[wll::export]
pub fn dtm_output_table_parallel_width_u64_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<u64> {
    let arr = dtm_output_table_parallel_width_u64(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    wll::NumericArray::from_array(&[num_rules, num_inputs], &arr)
}

#[wll::export]
pub fn dtm_output_table_parallel_steps_width_u64_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<u64> {
    let arr = dtm_output_table_parallel_steps_width_u64(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    wll::NumericArray::from_array(&[num_rules, num_inputs, 2], &arr)
}

/// WL wrapper returning (steps, value) pairs with full precision via WXF serialization.
#[wll::export]
pub fn dtm_output_table_parallel_steps_value_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<u8> {
    let table = dtm_output_table_parallel_steps_value(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table).unwrap())
}

/// WL wrapper returning a 3D NumericArray<f64> of triples (steps,value,width); non-halting has {0.0,-1.0,0.0}
#[wll::export]
pub fn dtm_output_table_triple_parallel_f64_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    min_rule: u64,
    max_rule: u64,
    min_input: u32,
    max_input: u32,
) -> wll::NumericArray<f64> {
    let arr = dtm_output_table_triple_parallel_f64(num_states, num_symbols, max_steps, min_rule, max_rule, min_input, max_input);
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    wll::NumericArray::from_array(&[num_rules, num_inputs, 3], &arr)
}

// =============================================================================
// Vec-based WL export wrappers
// =============================================================================

/// Parallel version of dtm_output_table_vec using rayon.
/// rules is now &[BigInt], inputs is &[BigUint]

#[wll::export]
pub fn dtm_output_table_parallel_vec_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: Vec<String>,
    inputs: Vec<String>,
) -> wll::NumericArray<u8> {
    let rules_big: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let inputs_big: Vec<BigUint> = inputs.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let table = dtm_output_table_parallel_vec(num_states, num_symbols, max_steps, &rules_big, &inputs_big);
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table).unwrap())
}

/// WL wrapper for vec-based triple parallel (returns WXF-serialized).
#[wll::export]
pub fn dtm_output_table_triple_parallel_vec_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: Vec<String>,
    inputs: Vec<String>,
) -> wll::NumericArray<u8> {
    let rules_big: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let inputs_big: Vec<BigUint> = inputs.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let table = dtm_output_table_triple_parallel_vec(num_states, num_symbols, max_steps, &rules_big, &inputs_big);
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table).unwrap())
}

#[wll::export]
pub fn dtm_output_table_parallel_steps_u64_vec_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: Vec<String>,
    inputs: Vec<String>,
) -> wll::NumericArray<u64> {
    let rules_big: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let inputs_big: Vec<BigUint> = inputs.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let arr = dtm_output_table_parallel_steps_u64_vec(num_states, num_symbols, max_steps, &rules_big, &inputs_big);
    let num_rules = rules_big.len();
    let num_inputs = inputs_big.len();
    wll::NumericArray::from_array(&[num_rules, num_inputs], &arr)
}

/// WL wrapper for vec-based width u64.
#[wll::export]
pub fn dtm_output_table_parallel_width_u64_vec_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: Vec<String>,
    inputs: Vec<String>,
) -> wll::NumericArray<u64> {
    let rules_big: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let inputs_big: Vec<BigUint> = inputs.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let arr = dtm_output_table_parallel_width_u64_vec(num_states, num_symbols, max_steps, &rules_big, &inputs_big);
    let num_rules = rules_big.len();
    let num_inputs = inputs_big.len();
    wll::NumericArray::from_array(&[num_rules, num_inputs], &arr)
}

/// WL wrapper for vec-based steps/width u64.
#[wll::export]
pub fn dtm_output_table_parallel_steps_width_u64_vec_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: Vec<String>,
    inputs: Vec<String>,
) -> wll::NumericArray<u64> {
    let rules_big: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let inputs_big: Vec<BigUint> = inputs.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let arr = dtm_output_table_parallel_steps_width_u64_vec(num_states, num_symbols, max_steps, &rules_big, &inputs_big);
    let num_rules = rules_big.len();
    let num_inputs = inputs_big.len();
    wll::NumericArray::from_array(&[num_rules, num_inputs * 2], &arr)
}

/// WL wrapper for vec-based f64 pairs.
#[wll::export]
pub fn dtm_output_table_pair_parallel_f64_vec_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: Vec<String>,
    inputs: Vec<String>,
) -> wll::NumericArray<f64> {
    let rules_big: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let inputs_big: Vec<BigUint> = inputs.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let arr = dtm_output_table_pair_parallel_f64_vec(num_states, num_symbols, max_steps, &rules_big, &inputs_big);
    let num_rules = rules_big.len();
    let num_inputs = inputs_big.len();
    wll::NumericArray::from_array(&[num_rules, num_inputs * 2], &arr)
}

/// WL wrapper for vec-based steps/value with full precision.
#[wll::export]
pub fn dtm_output_table_parallel_steps_value_vec_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: Vec<String>,
    inputs: Vec<String>,
) -> wll::NumericArray<u8> {
    let rules_big: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let inputs_big: Vec<BigUint> = inputs.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let table = dtm_output_table_parallel_steps_value_vec(num_states, num_symbols, max_steps, &rules_big, &inputs_big);
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table).unwrap())
}

/// WL wrapper for vec-based f64 triples.
#[wll::export]
pub fn dtm_output_table_triple_parallel_f64_vec_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: Vec<String>,
    inputs: Vec<String>,
) -> wll::NumericArray<f64> {
    let rules_big: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let inputs_big: Vec<BigUint> = inputs.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let arr = dtm_output_table_triple_parallel_f64_vec(num_states, num_symbols, max_steps, &rules_big, &inputs_big);
    let num_rules = rules_big.len();
    let num_inputs = inputs_big.len();
    wll::NumericArray::from_array(&[num_rules, num_inputs * 3], &arr)
}

/// WL wrapper for vec-based history (returns WXF-serialized).
#[wll::export]
pub fn dtm_output_table_triple_with_history_parallel_vec_wl(
    num_states: u32,
    num_symbols: u32,
    max_steps: u64,
    rules: Vec<String>,
    inputs: Vec<String>,
) -> wll::NumericArray<u8> {
    let rules_big: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let inputs_big: Vec<BigUint> = inputs.iter().map(|s| s.parse::<BigUint>().unwrap()).collect();
    let table = dtm_output_table_triple_with_history_parallel_vec(num_states, num_symbols, max_steps, &rules_big, &inputs_big);
    // Convert usize to u64 for WXF serialization
    let table_u64: Vec<Vec<Vec<(u32, u64, BigUint)>>> = table
        .into_iter()
        .map(|row| row.into_iter().map(|history| history.into_iter().map(|(s, p, v)| (s, p as u64, v)).collect()).collect())
        .collect();
    wll::NumericArray::from_slice(&wll::wxf_poly::to_wxf_bytes(&table_u64).unwrap())
}


#[wll::export]
pub fn collect_seen_values_tuples_wl(
    rules: Vec<(u32, u32, u32, u32, i32)>,
    num_states: u32,
    num_symbols: u32,
    initials: Vec<String>,
    targets: Vec<String>,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let tm = match TuringMachine::from_rule_tuples(&rules, num_states, num_symbols) {
        Ok(t) => t,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let initial_biguints: Vec<BigUint> = initials.iter().filter_map(|s| s.parse::<BigUint>().ok()).collect();
    let target_biguints: Vec<BigUint> = targets.iter().filter_map(|s| s.parse::<BigUint>().ok()).collect();
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguints, max_steps, &target_biguints, terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}

#[wll::export]
pub fn collect_seen_values_triples_wl(
    rules: Vec<(u32, u32, i32)>,
    num_states: u32,
    num_symbols: u32,
    initials: Vec<String>,
    targets: Vec<String>,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let tm = match TuringMachine::from_rule_triples(&rules, num_states, num_symbols) {
        Ok(t) => t,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let initial_biguints: Vec<BigUint> = initials.iter().filter_map(|s| s.parse::<BigUint>().ok()).collect();
    let target_biguints: Vec<BigUint> = targets.iter().filter_map(|s| s.parse::<BigUint>().ok()).collect();
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguints, max_steps, &target_biguints, terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}

#[wll::export]
pub fn collect_seen_values_tuples_inferred_wl(
    rules: Vec<(u32, u32, u32, u32, i32)>,
    initials: Vec<String>,
    targets: Vec<String>,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let tm = match TuringMachine::from_rule_tuples_inferred(&rules) {
        Ok(t) => t,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let initial_biguints: Vec<BigUint> = initials.iter().filter_map(|s| s.parse::<BigUint>().ok()).collect();
    let target_biguints: Vec<BigUint> = targets.iter().filter_map(|s| s.parse::<BigUint>().ok()).collect();
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguints, max_steps, &target_biguints, terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}

