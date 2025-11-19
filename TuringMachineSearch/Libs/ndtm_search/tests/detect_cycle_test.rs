use ndtm_search::{detect_cycle, models::{TuringMachine, TMState, Tape}};
use num_bigint::BigUint;

#[test]
fn test_detect_cycle_true() {
    // Construct a TM that cycles:
    // State 1, Sym 0 -> State 2, Sym 0, Left (+1)
    // State 2, Sym 0 -> State 1, Sym 0, Right (-1)
    // Start at (1, 0, [0]).
    // (1,0) -> (2,1) -> (1,0) ...
    
    let num_states = 2;
    let num_symbols = 2;
    // Triples: (next_state, write_symbol, direction)
    // Index: (state-1)*k + symbol
    // 0: (1,0) -> (2, 0, -1)
    // 1: (1,1) -> (1, 1, 1) (arbitrary)
    // 2: (2,0) -> (1, 0, 1)
    // 3: (2,1) -> (1, 1, 1) (arbitrary)
    
    let triples = vec![
        (2, 0, -1),
        (1, 1, 1),
        (1, 0, 1),
        (1, 1, 1),
    ];
    
    let tm = TuringMachine::from_rule_triples(&triples, num_states, num_symbols).unwrap();
    let initial = BigUint::from(0u32);
    let max_steps = 100;
    
    assert!(detect_cycle(&tm, &initial, max_steps));
}

#[test]
fn test_detect_cycle_false() {
    // Construct a TM that does not cycle (moves left forever):
    // State 1, Sym 0 -> State 1, Sym 0, Left (+1)
    
    let num_states = 2;
    let num_symbols = 2;
    // 0: (1,0) -> (1, 0, -1)
    
    let triples = vec![
        (1, 0, -1),
        (1, 1, 1),
        (1, 0, 1),
        (1, 1, 1),
    ];
    
    let tm = TuringMachine::from_rule_triples(&triples, num_states, num_symbols).unwrap();
    let initial = BigUint::from(0u32);
    let max_steps = 100;
    
    assert!(!detect_cycle(&tm, &initial, max_steps));
}
