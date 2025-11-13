use wolfram_library_link as wll;

wll::generate_loader!(rustlink_autodiscover);

use crate::models::{TMState, Tape, TuringMachine};
use num_bigint::{BigInt, BigUint};
use std::collections::{HashMap, HashSet, VecDeque};
use std::collections::BinaryHeap;

pub mod models;

// Provide a safe wrapper for abort checks that tolerates tests (no WL init)
#[inline]
fn aborted_safe() -> bool {
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use std::sync::atomic::{AtomicBool, Ordering};
    // Track whether we've successfully observed a working LibraryLink context.
    static AVAILABLE: AtomicBool = AtomicBool::new(false);
    // Track whether we've already tried (and possibly failed) to access it; avoid repeated panics.
    static TRIED_ONCE: AtomicBool = AtomicBool::new(false);

    if AVAILABLE.load(Ordering::Relaxed) {
        return wll::aborted();
    }
    if TRIED_ONCE.load(Ordering::Relaxed) {
        // We tried before and it wasn't available; treat as not aborted.
        return false;
    }
    // First (and only) probing attempt: catch potential panic caused by uninitialized LIBRARY_DATA.
    TRIED_ONCE.store(true, Ordering::Relaxed);
    match catch_unwind(AssertUnwindSafe(|| wll::aborted())) {
        Ok(v) => {
            AVAILABLE.store(true, Ordering::Relaxed);
            v
        }
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
) -> Option<(u64, BigUint)> {
    let initial_tape = Tape::from_integer(initial);
    let mut state = TMState {
        head_state: 1,
        head_position: 0,
        tape: initial_tape,
    };
    let mut steps: u64 = 0;

    while steps < max_steps {
        if aborted_safe() {
            return None;
        }
        let (halted, next_state) = tm.step_dtm(&state);
        state = next_state;
        steps += 1;
        if halted {
            let output = state.tape.to_integer();
            return Some((steps, output));
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
) -> (Vec<(u64, BigUint)>, usize) {
    let initial_tape = Tape::from_integer(initial);
    let initial_state = TMState {
        head_state: 1,
        head_position: 0,
        tape: initial_tape,
    };
    let mut queue: VecDeque<(TMState, u64)> = VecDeque::new();
    queue.push_back((initial_state.clone(), 0));
    let mut expanded: HashSet<TMState> = HashSet::new();
    // Maintain insertion order of unique halted values: Vec for ordered output, HashSet for membership test.
    let mut seen_order: Vec<(u64, BigUint)> = Vec::new();
    let mut seen_set: HashSet<BigUint> = HashSet::new();
    // Always include the initial tape value at step 0.
    let initial_val = initial_state.tape.to_integer();
    seen_order.push((0, initial_val.clone()));
    seen_set.insert(initial_val);
    let mut found_target = false;
    while let Some((current_state, depth)) = queue.pop_front() {
        if aborted_safe() || depth >= max_steps {
            break;
        }
        if expanded.contains(&current_state) {
            continue;
        }
        expanded.insert(current_state.clone());
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
        if found_target {
            break;
        }
    }
    (seen_order, queue.len())
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
) -> (u64, String) {
    let tm = match TuringMachine::from_rule_triples(&rule_triples, num_states, num_symbols) { Ok(t) => t, Err(_) => return (0, String::new()) };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() { Ok(v) => v, Err(_) => return (0, String::new()) };
    match run_dtm(&tm, &initial_biguint, max_steps) { Some((steps, out)) => (steps, out.to_string()), None => (0, String::new()) }
}

#[wll::export]
pub fn collect_seen_values_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    max_steps: u64,
) -> (Vec<(u64, String)>, usize) {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguint: BigUint = initial.parse::<BigUint>().unwrap();
    let (vals, remaining) = collect_seen_values(&tm, &initial_biguint, max_steps, None);
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), remaining)
}

#[wll::export]
pub fn collect_seen_values_with_target_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    target: String,
    max_steps: u64,
) -> (Vec<(u64, String)>, usize) {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|s| s.parse::<BigInt>().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_biguint: BigUint = initial.parse::<BigUint>().unwrap();
    let target_biguint: BigUint = target.parse::<BigUint>().unwrap();
    let (vals, remaining) = collect_seen_values(&tm, &initial_biguint, max_steps, Some(&target_biguint));
    (vals.into_iter().map(|(step, v)| (step, v.to_string())).collect(), remaining)
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
            if !rules.is_empty() {
                let mut variants: Vec<(u32, u32, i32)> = Vec::with_capacity(rules.len());
                for r in rules {
                    variants.push((r.next_state, r.write_symbol, if r.move_right { 1 } else { -1 }));
                }
                out.push(((state, symbol), variants));
            }
        }
    }
    out
}
