use wolfram_library_link as wll;

wll::generate_loader!(rustlink_autodiscover);

use crate::models::{TMState, Tape, TuringMachine};
use num_bigint::{BigInt, BigUint};
use std::collections::{HashMap, HashSet, VecDeque};
use std::collections::BinaryHeap;
use std::env;

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
    let debug_env = env::var("NDTM_DEBUG").unwrap_or_default();
    let debug: i32 = debug_env.parse().unwrap_or(-1);

    while let Some((current_state, depth)) = queue.pop_front() {
        // Cooperative abort: exit early if WL requested abort
        if aborted_safe() {
            if debug >= 0 {
                println!("[DBG] Abort requested by WL kernel; terminating search early");
            }
            return None;
        }
        let step = depth + 1;
        for (new_state, rule_num, halted) in tm.ndtm_step(&current_state) {
            if halted {
                let new_val = new_state.tape.to_integer();
                if seen_values.insert(new_val.clone()) {
                    if debug >= 0 {
                        println!("[DBG] Unique tape value found: {}", new_val);
                    }
                    if new_val == *target {
                        if debug >= 0 {
                            println!(
                                "[DBG] Target reached at step {} (after rule {})",
                                step, rule_num
                            );
                        }
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
    let debug_env = env::var("NDTM_DEBUG").unwrap_or_default();
    let debug: i32 = debug_env.parse().unwrap_or(-1);
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
                                if debug >= 0 {
                                    println!("[DBG] Thread found halted value: {}", new_val);
                                }
                                if new_val == target {
                                    if debug >= 0 {
                                        println!("[DBG] Target reached at depth {} (rule {})", depth+1, rule_num);
                                    }
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
    let debug_env = env::var("NDTM_DEBUG").unwrap_or_default();
    let debug: i32 = debug_env.parse().unwrap_or(-1);

    while steps < max_steps {
        if aborted_safe() {
            if debug >= 0 {
                println!("[DBG] Abort requested during run_dtm; terminating early");
            }
            return None;
        }
        let (halted, next_state) = tm.step_dtm(&state);
        state = next_state;
        steps += 1;
        if halted {
            let output = state.tape.to_integer();
            if debug >= 0 {
                println!(
                    "[DBG] run_dtm halted after {} steps with tape value {}",
                    steps, output
                );
            }
            return Some((steps, output));
        }
    }
    if debug >= 0 {
        println!(
            "[DBG] run_dtm did not halt within the provided step limit ({})",
            max_steps
        );
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
) -> Vec<(u64, BigUint)> {
    let initial_tape = Tape::from_integer(initial);
    let initial_state = TMState {
        head_state: 1,
        head_position: 0,
        tape: initial_tape,
    };
    let mut queue: VecDeque<(TMState, u64)> = VecDeque::new();
    queue.push_back((initial_state, 0));
    let mut expanded: HashSet<TMState> = HashSet::new();
    let mut seen_values: HashMap<BigUint, u64> = HashMap::new();
    let debug_env = env::var("NDTM_DEBUG").unwrap_or_default();
    let debug: i32 = debug_env.parse().unwrap_or(-1);
    let mut found_target = false;
    while let Some((current_state, depth)) = queue.pop_front() {
        if aborted_safe() {
            if debug >= 0 {
                println!("[DBG] Abort requested; early termination in collect_seen_values");
            }
            break; // return what we have so far
        }
        if expanded.contains(&current_state) {
            continue;
        }
        expanded.insert(current_state.clone());
        for (new_state, _rule_num, halted) in tm.ndtm_step(&current_state) {
            if halted {
                let val = new_state.tape.to_integer();
                if !seen_values.contains_key(&val) {
                    seen_values.insert(val.clone(), depth + 1);
                    if debug >= 0 {
                        println!("[DBG] (collect) unique halted tape value: {} at step {}", val, depth + 1);
                    }
                    if let Some(target_val) = target {
                        if &val == target_val {
                            found_target = true;
                            break;
                        }
                    }
                }
            } else if depth + 1 < max_steps {
                queue.push_back((new_state, depth + 1));
            }
        }
        if found_target {
            break;
        }
    }
    seen_values.into_iter().map(|(v, step)| (step, v)).collect()
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
    let rule_bigints: Vec<BigInt> = match rules
        .iter()
        .map(|s| s.parse::<BigInt>())
        .collect::<Result<Vec<_>, _>>()
    {
        Ok(v) => v,
        Err(_) => return Vec::new(),
    };
    let tm = match TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols) {
        Ok(t) => t,
        Err(_) => return Vec::new(),
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return Vec::new(),
    };
    let target_biguint: BigUint = match target.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return Vec::new(),
    };
    if aborted_safe() {
        return Vec::new();
    }
    match exhaustive_search_seq(&tm, &initial_biguint, &target_biguint, max_steps) {
        Some(path) => path.into_iter().map(|n| n.to_string()).collect(),
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
    let rule_bigints: Vec<BigInt> = match rules.iter().map(|s| s.parse::<BigInt>()).collect::<Result<Vec<_>, _>>() { Ok(v) => v, Err(_) => return Vec::new() };
    let tm = match TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols) { Ok(t) => t, Err(_) => return Vec::new() };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() { Ok(v) => v, Err(_) => return Vec::new() };
    let target_biguint: BigUint = match target.parse::<BigUint>() { Ok(v) => v, Err(_) => return Vec::new() };
    if aborted_safe() { return Vec::new(); }
    match exhaustive_search_parallel(&tm, &initial_biguint, &target_biguint, max_steps) {
        Some(path) => path.into_iter().map(|n| n.to_string()).collect(),
        None => Vec::new(),
    }
}

#[wll::export]
pub fn run_dtm_wl(
    rule: String,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    max_steps: u64,
) -> (u64, String) {
    let rule_bigint: BigInt = match rule.parse::<BigInt>() {
        Ok(v) => v,
        Err(_) => return (0, String::new()),
    };
    let tm = match TuringMachine::from_number(&rule_bigint, num_states, num_symbols) {
        Ok(t) => t,
        Err(_) => return (0, String::new()),
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return (0, String::new()),
    };
    if aborted_safe() {
        return (0, String::new());
    }
    match run_dtm(&tm, &initial_biguint, max_steps) {
        Some((steps, output)) => (steps, output.to_string()),
        None => (0, String::new()),
    }
}

#[wll::export]
pub fn collect_seen_values_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    max_steps: u64,
) -> Vec<(u64, String)> {
    let rule_bigints: Vec<BigInt> = match rules
        .iter()
        .map(|s| s.parse::<BigInt>())
        .collect::<Result<Vec<_>, _>>() {
        Ok(v) => v,
        Err(_) => return Vec::new(),
    };
    let tm = match TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols) {
        Ok(t) => t,
        Err(_) => return Vec::new(),
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return Vec::new(),
    };
    if aborted_safe() {
        return Vec::new();
    }
    let vals = collect_seen_values(&tm, &initial_biguint, max_steps, None);
    if aborted_safe() {
        return Vec::new();
    }
    vals.into_iter().map(|(step, v)| (step, v.to_string())).collect()
}

#[wll::export]
pub fn collect_seen_values_with_target_wl(
    rules: Vec<String>,
    num_states: u32,
    num_symbols: u32,
    initial: String,
    target: String,
    max_steps: u64,
) -> Vec<(u64, String)> {
    let rule_bigints: Vec<BigInt> = match rules
        .iter()
        .map(|s| s.parse::<BigInt>())
        .collect::<Result<Vec<_>, _>>() {
        Ok(v) => v,
        Err(_) => return Vec::new(),
    };
    let tm = match TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols) {
        Ok(t) => t,
        Err(_) => return Vec::new(),
    };
    let initial_biguint: BigUint = match initial.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return Vec::new(),
    };
    let target_biguint: BigUint = match target.parse::<BigUint>() {
        Ok(v) => v,
        Err(_) => return Vec::new(),
    };
    if aborted_safe() {
        return Vec::new();
    }
    let vals = collect_seen_values(&tm, &initial_biguint, max_steps, Some(&target_biguint));
    if aborted_safe() {
        return Vec::new();
    }
    vals.into_iter().map(|(step, v)| (step, v.to_string())).collect()
}
