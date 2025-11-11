// Add this to the top of the file to enable stdout printing for tests
#![cfg(test)]
use std::io::{self, Write};

fn print_test_header(name: &str) {
    let _ = writeln!(io::stdout(), "\n===== Running {} =====", name);
}

use ndtm_search::exhaustive_search;
use ndtm_search::models::{Rule, Tape, TuringMachine};
use ndtm_search::run_dtm;
use num_bigint::{BigUint, ToBigInt};

#[test]
fn test_run_dtm_halting() {
    print_test_header("test_run_dtm_halting");
    let mut rules = std::collections::HashMap::new();
    rules.insert(
        (1, 0),
        vec![Rule {
            rule_number: 42,
            next_state: 1,
            write_symbol: 1,
            move_right: true,
        }],
    );
    let tm = TuringMachine {
        rules,
        num_states: 1,
        num_symbols: 2,
    };
    let initial = BigUint::from(0u32);
    let result = run_dtm(&tm, &initial, 10).expect("machine should halt");
    assert_eq!(result.0, 1);
    assert_eq!(result.1, BigUint::from(1u32));
}

#[test]
fn test_run_dtm_non_halting_with_limit() {
    print_test_header("test_run_dtm_non_halting_with_limit");
    let mut rules = std::collections::HashMap::new();
    rules.insert(
        (1, 0),
        vec![Rule {
            rule_number: 7,
            next_state: 1,
            write_symbol: 0,
            move_right: false,
        }],
    );
    let tm = TuringMachine {
        rules,
        num_states: 1,
        num_symbols: 2,
    };
    let initial = BigUint::from(0u32);
    assert!(run_dtm(&tm, &initial, 5).is_none());
}

#[test]
fn test_tape_encoding_from_integer() {
    use ndtm_search::models::Tape;
    use num_bigint::BigUint;

    // 0 should produce a tape of length 1, all zeros
    let tape0 = Tape::from_integer(&BigUint::from(0u32));
    assert_eq!(tape0.len(), 1);
    assert_eq!(tape0.read(0), 0);

    // 1 should produce a tape of length 1, with a single 1
    let tape1 = Tape::from_integer(&BigUint::from(1u32));
    assert_eq!(tape1.len(), 1);
    assert_eq!(tape1.read(0), 1);

    // 2 should produce a tape of length 2, bits [0]=0, [1]=1
    let tape2 = Tape::from_integer(&BigUint::from(2u32));
    assert_eq!(tape2.len(), 2);
    assert_eq!(tape2.read(0), 0);
    assert_eq!(tape2.read(1), 1);

    // 3 should produce a tape of length 2, bits [0]=1, [1]=1
    let tape3 = Tape::from_integer(&BigUint::from(3u32));
    assert_eq!(tape3.len(), 2);
    assert_eq!(tape3.read(0), 1);
    assert_eq!(tape3.read(1), 1);

    // 8 should produce a tape of length 4, bits [0]=0, [1]=0, [2]=0, [3]=1
    let tape8 = Tape::from_integer(&BigUint::from(8u32));
    assert_eq!(tape8.len(), 4);
    assert_eq!(tape8.read(0), 0);
    assert_eq!(tape8.read(1), 0);
    assert_eq!(tape8.read(2), 0);
    assert_eq!(tape8.read(3), 1);

    // 255 should produce a tape of length 8, all ones
    let tape255 = Tape::from_integer(&BigUint::from(255u32));
    assert_eq!(tape255.len(), 8);
    for i in 0..8 {
        assert_eq!(tape255.read(i), 1);
    }
}

#[test]
fn test_tape_to_integer_round_trip() {
    print_test_header("test_tape_to_integer_round_trip");
    let cases = vec![
        BigUint::from(0u32),
        BigUint::from(1u32),
        BigUint::from(2u32),    // 10b
        BigUint::from(255u32),  // 0xFF
        BigUint::from(256u32),  // boundary to next byte
        BigUint::from(1024u32), // multi-byte with zeros
    ];
    for n in cases {
        let tape = Tape::from_integer(&n);
        let back = tape.to_integer();
        assert_eq!(back, n, "Round trip failed for {} -> {}", n, back);
    }
}

#[test]
fn test_tm_from_number_decoding() {
    print_test_header("test_tm_from_number_decoding");
    // Reference: TuringMachine[1285, {2, 2}]
    // {{1, 1} -> {1, 1, -1}, {1, 0} -> {2, 0, -1}, {2, 1} -> {1, 0, -1}, {2, 0} -> {2, 0, 1}}
    let n = 1285.to_bigint().unwrap();
    let s = 2;
    let k = 2;
    let tm = TuringMachine::from_number(&n, s, k).unwrap();

    assert_eq!(tm.num_states, s);
    assert_eq!(tm.num_symbols, k);
    assert_eq!(tm.rules.len(), (s * k) as usize);

    // {1, 1} -> {1, 1, -1}
    let rule1 = tm.get_rule(1, 1).unwrap();
    assert_eq!(rule1.next_state, 1);
    assert_eq!(rule1.write_symbol, 1);
    assert_eq!(rule1.move_right, false);

    // {1, 0} -> {2, 0, -1}
    let rule2 = tm.get_rule(1, 0).unwrap();
    assert_eq!(rule2.next_state, 2);
    assert_eq!(rule2.write_symbol, 0);
    assert_eq!(rule2.move_right, false);

    // {2, 1} -> {1, 0, -1}
    let rule3 = tm.get_rule(2, 1).unwrap();
    assert_eq!(rule3.next_state, 1);
    assert_eq!(rule3.write_symbol, 0);
    assert_eq!(rule3.move_right, false);

    // {2, 0} -> {2, 0, 1}
    let rule4 = tm.get_rule(2, 0).unwrap();
    assert_eq!(rule4.next_state, 2);
    assert_eq!(rule4.write_symbol, 0);
    assert_eq!(rule4.move_right, true);
}

#[test]
fn test_search_logic_with_ndtm() {
    print_test_header("test_search_logic_with_ndtm");
    let rule_nums = vec![3.to_bigint().unwrap(), 5.to_bigint().unwrap()];
    let tm = TuringMachine::from_numbers(&rule_nums, 1, 2).unwrap();
    let initial_val = BigUint::from(2u32);
    let target_val = BigUint::from(3u32);
    let _ = exhaustive_search(&tm, &initial_val, &target_val, 20);
    // All reached values are printed by exhaustive_search
}

#[test]
fn test_search_logic_with_two_state_ndtm() {
    print_test_header("test_search_logic_with_two_state_ndtm");
    let rule_nums = vec![
        2506.to_bigint().unwrap(),
        3506.to_bigint().unwrap(),
        1506.to_bigint().unwrap(),
    ];
    let tm = TuringMachine::from_numbers(&rule_nums, 2, 2).unwrap();
    let initial_val = BigUint::from(5u32);
    let target_val = BigUint::from(21u32);
    let _ = exhaustive_search(&tm, &initial_val, &target_val, 9);
    // All reached values are printed by exhaustive_search
}

#[test]
fn test_exhaustive_search_wl() {
    print_test_header("test_exhaustive_search_wl");
    let rules = vec![2506, 3506, 1506];
    let num_states = 2;
    let num_symbols = 2;
    let initial = 5;
    let target = 21;
    let max_steps = 100;

    let path = ndtm_search::exhaustive_search_wl(
        rules.clone(),
        num_states,
        num_symbols,
        initial,
        target,
        max_steps,
    );
    println!("Found path (len={}): {:?}", path.len(), path);
    assert!(!path.is_empty(), "A path should have been found");

    // Replay the path using deterministic step_dtm on a TM constructed for each rule number
    // Build a map of rule_number -> deterministic TuringMachine
    let mut tm_map: std::collections::HashMap<u64, TuringMachine> =
        std::collections::HashMap::new();
    for &r in &rules {
        let tm_single =
            TuringMachine::from_number(&r.to_bigint().unwrap(), num_states, num_symbols)
                .expect("Failed to construct deterministic TM for rule number");
        tm_map.insert(r, tm_single);
    }
    let mut state = ndtm_search::models::TMState {
        head_state: 1,
        head_position: 0,
        tape: Tape::from_integer(&BigUint::from(initial)),
    };
    for (step_idx, &rule_num) in path.iter().enumerate() {
        let tm_single = tm_map
            .get(&rule_num)
            .expect("Missing TM for rule number in map");
        let (halted, new_state) = tm_single.step_dtm(&state);
        println!(
            "Replay step {} rule {} -> head_state={} head_pos={} tape={}",
            step_idx,
            rule_num,
            new_state.head_state,
            new_state.head_position,
            new_state.tape.to_integer()
        );
        state = new_state;
        if halted {
            println!(
                "Halting after step {} (rule {}) with final tape={}",
                step_idx,
                rule_num,
                state.tape.to_integer()
            );
            break;
        }
    }
    let final_val = state.tape.to_integer();
    assert_eq!(
        final_val,
        BigUint::from(target),
        "Final tape value {} does not match target {}",
        final_val,
        target
    );
}
