#![cfg(test)]
use ndtm_search::models::{Tape, TuringMachine};
use ndtm_search::run_dtm;
use num_bigint::BigUint;

#[test]
fn test_tape_encoding_base3() {
    // Test base-3 (ternary) encoding
    // In base 3: 0 = 0, 1 = 1, 2 = 2, 3 = 10, 4 = 11, 5 = 12, 6 = 20, ...
    
    let tape0 = Tape::from_integer_base(&BigUint::from(0u32), 3);
    assert_eq!(tape0.len(), 1);
    assert_eq!(tape0.read(0), 0);
    
    let tape1 = Tape::from_integer_base(&BigUint::from(1u32), 3);
    assert_eq!(tape1.len(), 1);
    assert_eq!(tape1.read(0), 1);
    
    let tape2 = Tape::from_integer_base(&BigUint::from(2u32), 3);
    assert_eq!(tape2.len(), 1);
    assert_eq!(tape2.read(0), 2);
    
    // 3 in base 3 is "10" => [0, 1] (LSB first)
    let tape3 = Tape::from_integer_base(&BigUint::from(3u32), 3);
    assert_eq!(tape3.len(), 2);
    assert_eq!(tape3.read(0), 0);
    assert_eq!(tape3.read(1), 1);
    
    // 4 in base 3 is "11" => [1, 1]
    let tape4 = Tape::from_integer_base(&BigUint::from(4u32), 3);
    assert_eq!(tape4.len(), 2);
    assert_eq!(tape4.read(0), 1);
    assert_eq!(tape4.read(1), 1);
    
    // 5 in base 3 is "12" => [2, 1]
    let tape5 = Tape::from_integer_base(&BigUint::from(5u32), 3);
    assert_eq!(tape5.len(), 2);
    assert_eq!(tape5.read(0), 2);
    assert_eq!(tape5.read(1), 1);
    
    // 26 in base 3 is "222" => [2, 2, 2]
    let tape26 = Tape::from_integer_base(&BigUint::from(26u32), 3);
    assert_eq!(tape26.len(), 3);
    assert_eq!(tape26.read(0), 2);
    assert_eq!(tape26.read(1), 2);
    assert_eq!(tape26.read(2), 2);
}

#[test]
fn test_tape_encoding_base4() {
    // Test base-4 (quaternary) encoding
    // In base 4: 0 = 0, 1 = 1, 2 = 2, 3 = 3, 4 = 10, ...
    
    let tape0 = Tape::from_integer_base(&BigUint::from(0u32), 4);
    assert_eq!(tape0.len(), 1);
    assert_eq!(tape0.read(0), 0);
    
    let tape3 = Tape::from_integer_base(&BigUint::from(3u32), 4);
    assert_eq!(tape3.len(), 1);
    assert_eq!(tape3.read(0), 3);
    
    // 4 in base 4 is "10" => [0, 1]
    let tape4 = Tape::from_integer_base(&BigUint::from(4u32), 4);
    assert_eq!(tape4.len(), 2);
    assert_eq!(tape4.read(0), 0);
    assert_eq!(tape4.read(1), 1);
    
    // 15 in base 4 is "33" => [3, 3]
    let tape15 = Tape::from_integer_base(&BigUint::from(15u32), 4);
    assert_eq!(tape15.len(), 2);
    assert_eq!(tape15.read(0), 3);
    assert_eq!(tape15.read(1), 3);
    
    // 63 in base 4 is "333" => [3, 3, 3]
    let tape63 = Tape::from_integer_base(&BigUint::from(63u32), 4);
    assert_eq!(tape63.len(), 3);
    assert_eq!(tape63.read(0), 3);
    assert_eq!(tape63.read(1), 3);
    assert_eq!(tape63.read(2), 3);
}

#[test]
fn test_tape_round_trip_base3() {
    let cases = vec![
        BigUint::from(0u32),
        BigUint::from(1u32),
        BigUint::from(2u32),
        BigUint::from(3u32),
        BigUint::from(13u32),  // "111" in base 3
        BigUint::from(26u32),  // "222" in base 3
        BigUint::from(100u32),
    ];
    for n in cases {
        let tape = Tape::from_integer_base(&n, 3);
        let back = tape.to_integer();
        assert_eq!(back, n, "Round trip failed for {} in base 3", n);
    }
}

#[test]
fn test_tape_round_trip_base4() {
    let cases = vec![
        BigUint::from(0u32),
        BigUint::from(1u32),
        BigUint::from(4u32),
        BigUint::from(15u32),  // "33" in base 4
        BigUint::from(63u32),  // "333" in base 4
        BigUint::from(255u32), // "3333" in base 4
    ];
    for n in cases {
        let tape = Tape::from_integer_base(&n, 4);
        let back = tape.to_integer();
        assert_eq!(back, n, "Round trip failed for {} in base 4", n);
    }
}

#[test]
fn test_tape_write_base3() {
    let mut tape = Tape::from_integer_base(&BigUint::from(0u32), 3);
    
    // Write symbol 2 at position 0
    tape.write(0, 2);
    assert_eq!(tape.read(0), 2);
    assert_eq!(tape.to_integer(), BigUint::from(2u32));
    
    // Write symbol 1 at position 1 (extends tape)
    tape.write(1, 1);
    assert_eq!(tape.read(1), 1);
    // Tape is now [2, 1] = 2 + 1*3 = 5
    assert_eq!(tape.to_integer(), BigUint::from(5u32));
}

#[test]
fn test_tape_write_base4() {
    let mut tape = Tape::from_integer_base(&BigUint::from(0u32), 4);
    
    // Write symbol 3 at position 0
    tape.write(0, 3);
    assert_eq!(tape.read(0), 3);
    assert_eq!(tape.to_integer(), BigUint::from(3u32));
    
    // Write symbol 2 at position 1 (extends tape)
    tape.write(1, 2);
    assert_eq!(tape.read(1), 2);
    // Tape is now [3, 2] = 3 + 2*4 = 11
    assert_eq!(tape.to_integer(), BigUint::from(11u32));
}

#[test]
#[should_panic(expected = "out of range")]
fn test_tape_write_invalid_symbol_base3() {
    let mut tape = Tape::from_integer_base(&BigUint::from(0u32), 3);
    tape.write(0, 3); // Symbol 3 is invalid for base 3 (only 0, 1, 2 allowed)
}

#[test]
#[should_panic(expected = "out of range")]
fn test_tape_write_invalid_symbol_base4() {
    let mut tape = Tape::from_integer_base(&BigUint::from(0u32), 4);
    tape.write(0, 4); // Symbol 4 is invalid for base 4 (only 0, 1, 2, 3 allowed)
}

#[test]
fn test_tm_execution_base3_simple() {
    // Create a simple 1-state, 3-symbol TM
    // Rule: {1, 0} -> {1, 1, Right} (if reading 0, write 1 and move right)
    // This should halt when it tries to move right from position 0
    
    let triples = vec![
        (1, 1, 1),  // {1, 0} -> {1, 1, Right}
        (1, 0, -1), // {1, 1} -> {1, 0, Left}
        (1, 0, -1), // {1, 2} -> {1, 0, Left}
    ];
    
    let tm = TuringMachine::from_rule_triples(&triples, 1, 3).unwrap();
    
    // Start with input 0 (tape = [0])
    let initial = BigUint::from(0u32);
    let result = run_dtm(&tm, &initial, 10);
    
    // Should write 1 at position 0, then try to move right and halt
    assert!(result.is_some());
    let (steps, output, _width) = result.unwrap();
    assert_eq!(steps, 1);
    assert_eq!(output, BigUint::from(1u32));
}

#[test]
fn test_tm_execution_base4() {
    // Create a 1-state, 4-symbol TM
    // Rules that increment the symbol and halt on overflow
    let triples = vec![
        (1, 1, 1),   // {1, 0} -> {1, 1, Right}
        (1, 2, 1),   // {1, 1} -> {1, 2, Right}
        (1, 3, 1),   // {1, 2} -> {1, 3, Right}
        (1, 0, -1),  // {1, 3} -> {1, 0, Left} (wrap around and move left)
    ];
    
    let tm = TuringMachine::from_rule_triples(&triples, 1, 4).unwrap();
    
    // Start with input 0 (tape = [0])
    let initial = BigUint::from(0u32);
    let result = run_dtm(&tm, &initial, 10);
    
    // Should write 1 at position 0, then try to move right and halt
    assert!(result.is_some());
    let (steps, output, _width) = result.unwrap();
    assert_eq!(steps, 1);
    assert_eq!(output, BigUint::from(1u32));
}

#[test]
fn test_tm_multi_step_base3() {
    // Create a 2-state, 3-symbol TM that does some computation and halts
    // State 1, symbol 0: write 1, move right, go to state 2
    // State 1, symbol 1: write 2, move right, go to state 1
    // State 1, symbol 2: write 0, move left, stay in state 1
    // State 2, symbol 0: write 1, move right, halt (no rule, halts)
    // State 2, symbol 1: write 2, move right, go to state 2  
    // State 2, symbol 2: write 0, move right, go to state 1
    
    let triples = vec![
        (2, 1, 1),  // {1, 0} -> {2, 1, Right}
        (1, 2, 1),  // {1, 1} -> {1, 2, Right}
        (1, 0, -1), // {1, 2} -> {1, 0, Left}
        (1, 1, 1),  // {2, 0} -> {1, 1, Right} - this makes it halt by going to position 0 and moving right
        (2, 2, 1),  // {2, 1} -> {2, 2, Right}
        (1, 0, 1),  // {2, 2} -> {1, 0, Right}
    ];
    
    let tm = TuringMachine::from_rule_triples(&triples, 2, 3).unwrap();
    
    // Start with tape [0]
    let initial = BigUint::from(0u32);
    let result = run_dtm(&tm, &initial, 20);
    
    // The machine should halt within 20 steps
    assert!(result.is_some(), "TM should halt");
    let (_steps, output, _width) = result.unwrap();
    println!("Final output: {}", output);
}

#[test]
fn test_binary_tape_still_works() {
    // Ensure binary tapes still work with default from_integer
    let tape = Tape::from_integer(&BigUint::from(5u32));
    assert_eq!(tape.read(0), 1); // LSB of 5 (binary 101)
    assert_eq!(tape.read(1), 0);
    assert_eq!(tape.read(2), 1);
    assert_eq!(tape.to_integer(), BigUint::from(5u32));
}

#[test]
fn test_binary_vs_explicit_base2() {
    // from_integer should be equivalent to from_integer_base(n, 2)
    for i in 0..20u32 {
        let n = BigUint::from(i);
        let tape1 = Tape::from_integer(&n);
        let tape2 = Tape::from_integer_base(&n, 2);
        assert_eq!(tape1.to_integer(), tape2.to_integer());
        assert_eq!(tape1.len(), tape2.len());
    }
}
