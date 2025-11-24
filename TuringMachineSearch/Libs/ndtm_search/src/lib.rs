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
    (min_rule..=max_rule)
        .into_par_iter()
        .map(|rule_num| {
            if aborted_safe() { return Vec::new(); }
            let n_bigint = BigInt::from(rule_num);
            let tm = match models::TuringMachine::from_number(&n_bigint, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return Vec::new(),
            };
            if min_input > max_input { return Vec::new(); }
            (min_input..=max_input)
                .map(|input| {
                    if aborted_safe() { return None; }
                    let input_big = BigUint::from(input);
                    run_dtm(&tm, &input_big, max_steps).map(|(_s, out, _maxw)| out)
                })
                .collect()
        })
        .collect()
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
    let mut table: Vec<Vec<Option<(u64, BigUint, u64)>>> = Vec::with_capacity(rule_space_size as usize);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    for rule_num in min_rule..=max_rule {
        if aborted_safe() { break; }
        let n_bigint = BigInt::from(rule_num);
        let tm = match models::TuringMachine::from_number(&n_bigint, num_states, num_symbols) {
            Ok(t) => t,
            Err(_) => { table.push(Vec::new()); continue; }
        };
    if min_input > max_input { table.push(Vec::new()); continue; }
    let mut row: Vec<Option<(u64, BigUint, u64)>> = Vec::with_capacity((max_input - min_input + 1) as usize);
    for input in min_input..=max_input {
            if aborted_safe() { break; }
            let input_big = BigUint::from(input);
            let result = run_dtm(&tm, &input_big, max_steps);
            row.push(result.map(|(s, out, maxw)| (s, out, maxw)));
        }
        table.push(row);
    }
    table
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
    (min_rule..=max_rule)
        .into_par_iter()
        .map(|rule_num| {
            if aborted_safe() { return Vec::new(); }
            let n_bigint = BigInt::from(rule_num);
            let tm = match models::TuringMachine::from_number(&n_bigint, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return Vec::new(),
            };
            if min_input > max_input { return Vec::new(); }
            (min_input..=max_input)
                .map(|input| {
                    if aborted_safe() { return None; }
                    let input_big = BigUint::from(input);
                    run_dtm(&tm, &input_big, max_steps).map(|(s, out, pos)| (s, out, pos + 1))
                })
                .collect()
        })
        .collect()
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
    use std::sync::{Arc, Mutex};
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    let out = Arc::new(Mutex::new(vec![0.0; num_rules * num_inputs * 2]));
    (min_rule..=max_rule).into_par_iter().for_each(|rule_num| {
        let rule_idx_val = (rule_num - min_rule) as usize;
        if aborted_safe() { return; }
        let n_bigint = BigInt::from(rule_num);
        let tm = match models::TuringMachine::from_number(&n_bigint, num_states, num_symbols) {
            Ok(t) => t,
            Err(_) => return,
        };
        for (input_idx, input) in (min_input..=max_input).enumerate() {
            if aborted_safe() { return; }
            let input_big = BigUint::from(input);
            let result = run_dtm(&tm, &input_big, max_steps);
            let offset = (rule_idx_val * num_inputs + input_idx) * 2;
            let mut out_guard = out.lock().unwrap();
                match result {
                Some((steps, value, _maxw)) => {
                    out_guard[offset] = steps as f64;
                    out_guard[offset + 1] = value.to_f64().unwrap_or(0.0);
                },
                None => {
                    out_guard[offset] = 0.0;
                    out_guard[offset + 1] = -1.0;
                }
            }
        }
    });
    match Arc::try_unwrap(out) {
        Ok(mutex) => mutex.into_inner().unwrap(),
        Err(arc) => arc.lock().unwrap().clone(),
    }
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
    let rows: Vec<Vec<u64>> = (min_rule..=max_rule)
        .into_par_iter()
        .map(|rule_num| {
            if aborted_safe() { return Vec::new(); }
            let n_bigint = BigInt::from(rule_num);
            let tm = match models::TuringMachine::from_number(&n_bigint, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return Vec::new(),
            };
            (min_input..=max_input)
                .map(|input| {
                    if aborted_safe() { return 0u64; }
                    let input_big = BigUint::from(input);
                    match run_dtm(&tm, &input_big, max_steps) { Some((steps,_,_)) => steps, None => 0 }
                })
                .collect()
        })
        .collect();
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    let mut out = Vec::with_capacity(num_rules * num_inputs);
    for row in rows { out.extend(row); }
    out
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
    let rows: Vec<Vec<u64>> = (min_rule..=max_rule)
        .into_par_iter()
        .map(|rule_num| {
            if aborted_safe() { return Vec::new(); }
            let n_bigint = BigInt::from(rule_num);
            let tm = match models::TuringMachine::from_number(&n_bigint, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return Vec::new(),
            };
            (min_input..=max_input)
                .map(|input| {
                    if aborted_safe() { return 0u64; }
                    let input_big = BigUint::from(input);
                    match run_dtm(&tm, &input_big, max_steps) { Some((_,_,pos)) => pos + 1, None => 0 }
                })
                .collect()
        })
        .collect();
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    let mut out = Vec::with_capacity(num_rules * num_inputs);
    for row in rows { out.extend(row); }
    out
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
    let rows: Vec<Vec<u64>> = (min_rule..=max_rule)
        .into_par_iter()
        .map(|rule_num| {
            if aborted_safe() { return Vec::new(); }
            let n_bigint = BigInt::from(rule_num);
            let tm = match models::TuringMachine::from_number(&n_bigint, num_states, num_symbols) {
                Ok(t) => t,
                Err(_) => return Vec::new(),
            };
            (min_input..=max_input)
                .map(|input| {
                    if aborted_safe() { return vec![0u64, 0u64]; }
                    let input_big = BigUint::from(input);
                    match run_dtm(&tm, &input_big, max_steps) {
                        Some((steps, _, pos)) => vec![steps, pos + 1],
                        None => vec![0u64, 0u64]
                    }
                })
                .flatten()
                .collect()
        })
        .collect();
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    let mut out = Vec::with_capacity(num_rules * num_inputs * 2);
    for row in rows { out.extend(row); }
    out
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
    use std::sync::{Arc, Mutex};
    let base: u64 = (2 * num_states * num_symbols) as u64;
    let exp: u32 = (num_states * num_symbols) as u32;
    let rule_space_size: u64 = base.pow(exp);
    if min_rule > max_rule || max_rule >= rule_space_size { return Vec::new(); }
    let num_rules = (max_rule - min_rule + 1) as usize;
    let num_inputs = (max_input - min_input + 1) as usize;
    let out = Arc::new(Mutex::new(vec![0.0; num_rules * num_inputs * 3]));
    (min_rule..=max_rule).into_par_iter().for_each(|rule_num| {
        let rule_idx_val = (rule_num - min_rule) as usize;
        if aborted_safe() { return; }
        let n_bigint = BigInt::from(rule_num);
        let tm = match models::TuringMachine::from_number(&n_bigint, num_states, num_symbols) {
            Ok(t) => t,
            Err(_) => return,
        };
        for (input_idx, input) in (min_input..=max_input).enumerate() {
            if aborted_safe() { return; }
            let input_big = BigUint::from(input);
            let result = run_dtm(&tm, &input_big, max_steps);
            let offset = (rule_idx_val * num_inputs + input_idx) * 3;
            let mut out_guard = out.lock().unwrap();
            match result {
                Some((steps, value, pos)) => {
                    out_guard[offset] = steps as f64;
                    out_guard[offset + 1] = value.to_f64().unwrap_or(0.0);
                    out_guard[offset + 2] = (pos + 1) as f64;
                }
                None => {
                    out_guard[offset] = 0.0;
                    out_guard[offset + 1] = -1.0; // sentinel for non-halting value
                    out_guard[offset + 2] = 0.0;  // width 0 for non-halting
                }
            }
        }
    });
    match Arc::try_unwrap(out) {
        Ok(mutex) => mutex.into_inner().unwrap(),
        Err(arc) => arc.lock().unwrap().clone(),
    }
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
pub fn exhaustive_search_seq(
    tm: &TuringMachine,
    initial: &BigUint,
    target: &BigUint,
    max_steps: u64,
) -> Option<Vec<u64>> {
    let initial_tape = Tape::from_integer(initial);
    let initial_state = TMState {
        head_state: 1,
        head_position: 0,
        tape: initial_tape,
    };
    let mut queue: VecDeque<(TMState, u64)> = VecDeque::new();
    queue.push_back((initial_state.clone(), 0));
    let mut expanded: HashMap<TMState, (Option<TMState>, Option<u64>)> = HashMap::new();
    expanded.insert(initial_state, (None, None));
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
                    if new_val == *target {
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
pub fn exhaustive_search_parallel(
    tm: &TuringMachine,
    initial: &BigUint,
    target: &BigUint,
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
    // Compute bit difference heuristic between current tape value and target value.
    fn bit_diff(a: &BigUint, b: &BigUint) -> usize { use num_traits::Zero; if a.is_zero() { return b.bits() as usize; } if b.is_zero() { return a.bits() as usize; } let xor = a ^ b; xor.bits() as usize }
    let initial_tape = Tape::from_integer(initial);
    let initial_state = TMState { head_state: 1, head_position: 0, tape: initial_tape };
    let heap: Arc<Mutex<BinaryHeap<ScoredState>>> = Arc::new(Mutex::new(BinaryHeap::new()));
    {
        let initial_val = initial_state.tape.to_integer();
        let score = bit_diff(&initial_val, target);
        heap.lock().unwrap().push(ScoredState { score, depth: 0, state: initial_state.clone(), path: Vec::new() });
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
            let target = target.clone();
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
                                if new_val == target {
                                    found.store(true, Ordering::SeqCst);
                                    *result_path.lock().unwrap() = Some(new_path);
                                    active_workers.fetch_sub(1, Ordering::SeqCst);
                                    break;
                                }
                            } else {
                                let new_val = ns.tape.to_integer();
                                let score = bit_diff(&new_val, &target);
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
    let initial_tape = Tape::from_integer(initial);
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
        if aborted_safe() {
            return None;
        }
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

/// Traverse the non-deterministic TM and collect all unique halted tape values encountered.
/// No path information is retained; traversal stops after reaching `max_steps` depth.
/// Returns Vec<(u64, BigUint)> where u64 is the step at which the value was found.
/// If target is Some, terminates early if target value is found.
pub fn collect_seen_values(
    tm: &TuringMachine,
    initial: &BigUint,
    max_steps: u64,
    target: Option<&BigUint>,
    terminate_on_cycle: bool,
) -> (Vec<(u64, BigUint)>, Vec<usize>, bool) {
    let initial_tape = Tape::from_integer(initial);
    let initial_state = TMState {
        head_state: 1,
        head_position: 0,
        tape: initial_tape,
    };
    let mut queue: VecDeque<(TMState, u64)> = VecDeque::new();
    queue.push_back((initial_state.clone(), 0));
    // Track insertion depth of each expanded state
    let mut expanded: HashMap<TMState, u64> = HashMap::new();
    let mut seen_order: Vec<(u64, BigUint)> = Vec::new();
    let mut seen_set: HashSet<BigUint> = HashSet::new();
    let mut found_target = false;
    let mut queue_sizes: Vec<usize> = Vec::new();
    queue_sizes.push(1); // initial queue size
    let mut cycle_detected = false;
    let mut last_depth = 0u64;
    while let Some((current_state, depth)) = queue.pop_front() {
        if depth > last_depth {
            // +1 for the current popped state
            queue_sizes.push(queue.len() + 1);
            last_depth = depth;
        }
        if aborted_safe() || depth >= max_steps { break; }
        if let Some(prev_depth) = expanded.get(&current_state) {
            // Cycle if we encounter same state at a greater depth
            if depth > *prev_depth {
                cycle_detected = true;
                if terminate_on_cycle { break; }
            }
            continue; // don't expand again
        } else {
            expanded.insert(current_state.clone(), depth);
        }
        for (new_state, _rule_num, halted) in tm.ndtm_step(&current_state) {
            if halted {
                let val = new_state.tape.to_integer();
                if !seen_set.contains(&val) {
                    seen_set.insert(val.clone());
                    seen_order.push((depth + 1, val.clone()));
                    if let Some(target_val) = target {
                        if &val == target_val {
                            found_target = true;
                            break;
                        }
                    }
                }
            } else {
                queue.push_back((new_state, depth + 1));
            }
        }
        if found_target { break; }
    }
    queue_sizes.push(queue.len());
    (seen_order, queue_sizes, cycle_detected)
}

/// Detect if the non-deterministic TM enters a cycle within max_steps.
/// Returns true if a cycle is detected, false otherwise.
pub fn detect_cycle(
    tm: &TuringMachine,
    initial: &BigUint,
    max_steps: u64,
) -> bool {
    let initial_tape = Tape::from_integer(initial);
    let initial_state = TMState {
        head_state: 1,
        head_position: 0,
        tape: initial_tape,
    };
    let mut queue: VecDeque<(TMState, u64)> = VecDeque::new();
    queue.push_back((initial_state.clone(), 0));
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
pub fn ndtm_traverse_queue_size(
    tm: &TuringMachine,
    initial: &BigUint,
    max_steps: u64,
) -> usize {
    let initial_tape = Tape::from_integer(initial);
    let initial_state = TMState { head_state: 1, head_position: 0, tape: initial_tape };
    let mut queue: VecDeque<(TMState, u64)> = VecDeque::new();
    queue.push_back((initial_state, 0));
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
    initial: String,
    target: String,
    max_steps: u64,
) -> Vec<String> {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguint: BigUint = initial.parse::<BigUint>().unwrap();
    let target_biguint: BigUint = target.parse::<BigUint>().unwrap();
    match exhaustive_search_seq(&tm, &initial_biguint, &target_biguint, max_steps) {
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
    initial: String,
    target: String,
    max_steps: u64,
) -> Vec<String> {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguint: BigUint = initial.parse::<BigUint>().unwrap();
    let target_biguint: BigUint = target.parse::<BigUint>().unwrap();
    match exhaustive_search_parallel(&tm, &initial_biguint, &target_biguint, max_steps) {
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
pub fn collect_seen_values_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguint: BigUint = initial.parse::<BigUint>().unwrap();
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguint, max_steps, None, terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}

#[wll::export]
pub fn collect_seen_values_with_target_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    target: String,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguint: BigUint = initial.parse::<BigUint>().unwrap();
    let target_biguint: BigUint = target.parse::<BigUint>().unwrap();
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguint, max_steps, Some(&target_biguint), terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}

#[wll::export]
pub fn detect_cycle_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    max_steps: u64,
) -> bool {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguint: BigUint = initial.parse::<BigUint>().unwrap();
    detect_cycle(&tm, &initial_biguint, max_steps)
}

#[wll::export]
pub fn ndtm_traverse_queue_size_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    max_steps: u64,
) -> usize {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguint: BigUint = initial.parse::<BigUint>().unwrap();
    ndtm_traverse_queue_size(&tm, &initial_biguint, max_steps)
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

#[wll::export]
pub fn collect_seen_values_tuples_wl(
    rules: Vec<(u32, u32, u32, u32, i32)>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let tm = match TuringMachine::from_rule_tuples(&rules, num_states, num_symbols) {
        Ok(t) => t,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguint, max_steps, None, terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}

#[wll::export]
pub fn collect_seen_values_with_target_tuples_wl(
    rules: Vec<(u32, u32, u32, u32, i32)>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    target: String,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let tm = match TuringMachine::from_rule_tuples(&rules, num_states, num_symbols) {
        Ok(t) => t,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let target_biguint: BigUint = match target.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguint, max_steps, Some(&target_biguint), terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}

#[wll::export]
pub fn collect_seen_values_triples_wl(
    rules: Vec<(u32, u32, i32)>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let tm = match TuringMachine::from_rule_triples(&rules, num_states, num_symbols) {
        Ok(t) => t,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguint, max_steps, None, terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}

#[wll::export]
pub fn collect_seen_values_with_target_triples_wl(
    rules: Vec<(u32, u32, i32)>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    target: String,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let tm = match TuringMachine::from_rule_triples(&rules, num_states, num_symbols) {
        Ok(t) => t,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let target_biguint: BigUint = match target.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguint, max_steps, Some(&target_biguint), terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}


#[wll::export]
pub fn collect_seen_values_tuples_inferred_wl(
    rules: Vec<(u32, u32, u32, u32, i32)>,
    initial: String,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let tm = match TuringMachine::from_rule_tuples_inferred(&rules) {
        Ok(t) => t,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguint, max_steps, None, terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}

#[wll::export]
pub fn collect_seen_values_with_target_tuples_inferred_wl(
    rules: Vec<(u32, u32, u32, u32, i32)>,
    initial: String,
    target: String,
    max_steps: u64,
    terminate_on_cycle: bool,
) -> (Vec<(u64, String)>, Vec<usize>, bool) {
    let tm = match TuringMachine::from_rule_tuples_inferred(&rules) {
        Ok(t) => t,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let target_biguint: BigUint = match target.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return (Vec::new(), Vec::new(), false),
    };
    let (vals, queue_sizes, cycle_detected) = collect_seen_values(&tm, &initial_biguint, max_steps, Some(&target_biguint), terminate_on_cycle);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), queue_sizes, cycle_detected)
}
