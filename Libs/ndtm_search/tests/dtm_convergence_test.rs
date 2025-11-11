use ndtm_search::models::{TMState, Tape, TuringMachine};
use num_bigint::{BigUint, ToBigInt};

fn run_dtm_simulation(tm: &TuringMachine, initial_integer: &BigUint, max_steps: u32) -> BigUint {
    if initial_integer == &BigUint::from(0u32) {
        return BigUint::from(0u32);
    }
    let initial_tape = Tape::from_integer(initial_integer);

    let mut current_state = TMState {
        head_state: 1,    // DTM starts at state 1
        head_position: 0, // Start at the actual LSB
        tape: initial_tape,
    };

    for _ in 0..max_steps {
        let (halted, next_state) = tm.step_dtm(&current_state);
        if halted {
            return next_state.tape.to_integer();
        }
        current_state = next_state;
    }

    // Max steps reached, return current tape value
    current_state.tape.to_integer()
}

#[test]
fn test_dtm_rules_convergence() {
    let rule_ids = vec![1285, 261, 3333];
    let s = 2; // num_states
    let k = 2; // num_symbols
    let max_steps = 50;
    let expected_outputs: Vec<u32> = vec![
        0, 0, 0, 4, 0, 0, 0, 8, 8, 0, 0, 12, 0, 0, 0, 16, 16, 16, 16, 20, 0, 0, 0, 24, 24, 0, 0,
        28, 0, 0, 0, 32, 32, 32, 32,
    ];

    let mut results_per_rule = Vec::new();

    for rule_id in &rule_ids {
        let n = rule_id.to_bigint().unwrap();
        let tm = TuringMachine::from_number(&n, s, k).unwrap();
        let mut outputs = Vec::new();
        for i in 1..=35 {
            let initial_integer = BigUint::from(i as u32);
            let output = run_dtm_simulation(&tm, &initial_integer, max_steps);
            outputs.push(output);
        }
        results_per_rule.push(outputs);
    }

    // Check that all rule sets produce the same sequence of outputs
    for i in 1..results_per_rule.len() {
        assert_eq!(
            results_per_rule[0], results_per_rule[i],
            "Output sequences for rule {} and {} do not match!",
            rule_ids[0], rule_ids[i]
        );
    }

    // Check if the sequence matches the expected one
    let final_outputs_u32: Vec<u32> = results_per_rule[0]
        .iter()
        .map(|n| n.try_into().unwrap_or(u32::MAX))
        .collect();

    assert_eq!(final_outputs_u32, expected_outputs);
}
