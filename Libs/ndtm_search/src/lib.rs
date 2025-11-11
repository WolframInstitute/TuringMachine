use wolfram_library_link as wll;

wll::generate_loader!(rustlink_autodiscover);


use crate::models::{TuringMachine, Tape, TMState, SearchNode};
use num_bigint::{BigInt, BigUint, ToBigInt};
use num_traits::ToPrimitive;
use std::collections::{HashSet, VecDeque};
use std::env;

pub mod models;

// Provide a safe wrapper for abort checks that tolerates tests (no WL init)
#[inline]
fn aborted_safe() -> bool {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::panic::{catch_unwind, AssertUnwindSafe};
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

/// Exhaustive search for target value using non-deterministic TM
/// Returns a path of (rule_number, halted) for each step
pub fn exhaustive_search(
    tm: &TuringMachine,
    initial: &BigUint,
    target: &BigUint,
    max_steps: u32,
) -> Option<Vec<u64>> {
    let initial_tape = Tape::from_integer(initial);
    let initial_state = TMState { head_state: 1, head_position: 0, tape: initial_tape };
    let mut queue = VecDeque::new();
    queue.push_back(SearchNode { state: initial_state, path: Vec::new() });
    let mut expanded: HashSet<TMState> = HashSet::new();
    let mut seen_values: HashSet<BigUint> = HashSet::new();
    let debug_env = env::var("NDTM_DEBUG").unwrap_or_default();
    let debug: i32 = debug_env.parse().unwrap_or(-1);

    while let Some(current_node) = queue.pop_front() {
        // Cooperative abort: exit early if WL requested abort
        if aborted_safe() {
            if debug >= 0 { println!("[DBG] Abort requested by WL kernel; terminating search early"); }
            return None;
        }
        let step = current_node.path.len() + 1;
        if expanded.contains(&current_node.state) { continue; }
        expanded.insert(current_node.state.clone());
        for (new_state, rule_num, halted) in tm.ndtm_step(&current_node.state) {
            let mut new_path = current_node.path.clone();
            new_path.push(rule_num);
            if halted {
                let new_val = new_state.tape.to_integer();
                if seen_values.insert(new_val.clone()) {
                    if debug >= 0 {
                        println!("[DBG] Unique tape value found: {}", new_val);
                    }
                    if new_val == *target {
                        if debug >= 0 { println!("[DBG] Target reached at step {} (after rule {})", step, rule_num); }
                        return Some(new_path);
                    }
                }
            } else {
                if step < max_steps as usize {
                    queue.push_back(SearchNode { state: new_state, path: new_path });
                }
            }
        }
    }
    None
}

/// Traverse the non-deterministic TM and collect all unique halted tape values encountered.
/// Returns the set of unique tape integers (converted to u64; values > u64::MAX are skipped).
/// No path information is retained; traversal stops after reaching `max_steps` depth.
pub fn collect_seen_values(
    tm: &TuringMachine,
    initial: &BigUint,
    max_steps: u32,
) -> Vec<BigUint> {
    let initial_tape = Tape::from_integer(initial);
    let initial_state = TMState { head_state: 1, head_position: 0, tape: initial_tape };
    let mut queue: VecDeque<(TMState, usize)> = VecDeque::new();
    queue.push_back((initial_state, 0));
    let mut expanded: HashSet<TMState> = HashSet::new();
    let mut seen_values: HashSet<BigUint> = HashSet::new();
    let debug_env = env::var("NDTM_DEBUG").unwrap_or_default();
    let debug: i32 = debug_env.parse().unwrap_or(-1);

    while let Some((current_state, depth)) = queue.pop_front() {
        if aborted_safe() {
            if debug >= 0 { println!("[DBG] Abort requested; early termination in collect_seen_values"); }
            break; // return what we have so far
        }
        if expanded.contains(&current_state) { continue; }
        expanded.insert(current_state.clone());
        for (new_state, _rule_num, halted) in tm.ndtm_step(&current_state) {
            if halted {
                let val = new_state.tape.to_integer();
                if seen_values.insert(val.clone()) && debug >= 0 {
                    println!("[DBG] (collect) unique halted tape value: {}", val);
                }
            } else if depth + 1 < max_steps as usize {
                queue.push_back((new_state, depth + 1));
            }
        }
    }
    seen_values.into_iter().collect()
}


#[wll::export]
pub fn exhaustive_search_wl(
    rules: Vec<u64>,
    num_states: u32,
    num_symbols: u32,
    initial: u64,
    target: u64,
    max_steps: u32,
) -> Vec<u64> {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|&n| n.to_bigint().unwrap()).collect();
    let tm = TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols).unwrap();
    let initial_bigint = initial.to_bigint().unwrap().to_biguint().unwrap();
    let target_bigint = target.to_bigint().unwrap().to_biguint().unwrap();
    if std::env::var("NDTM_DEBUG").ok().filter(|v| v=="1" || v.eq_ignore_ascii_case("true")).is_some() {
        println!("[DBG] exhaustive_search_wl initial={} target={} rules={:?}", initial_bigint, target_bigint, rules);
    }

    if aborted_safe() {
        return Vec::new();
    }
    exhaustive_search(&tm, &initial_bigint, &target_bigint, max_steps).unwrap_or_default()
}

#[wll::export]
pub fn collect_seen_values_wl(
    rules: Vec<u64>,
    num_states: u32,
    num_symbols: u32,
    initial: u64,
    max_steps: u32,
) -> Vec<u64> {
    let rule_bigints: Vec<BigInt> = rules.iter().map(|&n| n.to_bigint().unwrap()).collect();
    let tm = match TuringMachine::from_numbers(&rule_bigints, num_states, num_symbols) { Ok(t) => t, Err(_) => return Vec::new() };
    let initial_bigint = match initial.to_bigint().unwrap().to_biguint() { Some(b) => b, None => return Vec::new() };
    if aborted_safe() { return Vec::new(); }
    let vals = collect_seen_values(&tm, &initial_bigint, max_steps);
    // Map to u64, skip those that don't fit
    vals.into_iter().filter_map(|v| v.to_u64()).collect()
}
