use wolfram_library_link as wll;

wll::generate_loader!(rustlink_autodiscover);

use crate::models::{TMState, Tape, TuringMachine};
use num_bigint::{BigInt, BigUint};
use std::collections::{HashMap, HashSet, VecDeque};
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

/// Exhaustive search for target value using non-deterministic TM
/// Returns a path of (rule_number, halted) for each step
pub fn exhaustive_search(
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
            if expanded.contains_key(&new_state) {
                continue;
            }
            expanded.insert(
                new_state.clone(),
                (Some(current_state.clone()), Some(rule_num)),
            );
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
                        return Some(reconstruct_path(&expanded, new_state));
                    }
                }
            } else {
                if step < max_steps {
                    queue.push_back((new_state, depth + 1));
                }
            }
        }
    }
    None
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
/// Returns the set of unique tape integers (converted to u64; values > u64::MAX are skipped).
/// No path information is retained; traversal stops after reaching `max_steps` depth.
pub fn collect_seen_values(tm: &TuringMachine, initial: &BigUint, max_steps: u32) -> Vec<BigUint> {
    let initial_tape = Tape::from_integer(initial);
    let initial_state = TMState {
        head_state: 1,
        head_position: 0,
        tape: initial_tape,
    };
    let mut queue: VecDeque<(TMState, usize)> = VecDeque::new();
    queue.push_back((initial_state, 0));
    let mut expanded: HashSet<TMState> = HashSet::new();
    let mut seen_values: HashSet<BigUint> = HashSet::new();
    let debug_env = env::var("NDTM_DEBUG").unwrap_or_default();
    let debug: i32 = debug_env.parse().unwrap_or(-1);

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
    match exhaustive_search(&tm, &initial_biguint, &target_biguint, max_steps) {
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
    max_steps: u32,
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
    if aborted_safe() {
        return Vec::new();
    }
    let vals = collect_seen_values(&tm, &initial_biguint, max_steps);
    vals.into_iter().map(|v| v.to_string()).collect()
}
