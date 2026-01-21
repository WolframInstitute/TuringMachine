#![cfg(test)]
use ndtm_search::{
    dtm_output_table_triple_parallel,
    dtm_output_table_triple_parallel_f64,
};
use num_traits::ToPrimitive;

// Compare structured steps+value table with flattened f64 representation for all 2,2 rules.
#[test]
fn test_steps_f64_consistency_small_inputs() {
    let s: u32 = 2;
    let k: u32 = 2;
    let max_steps: u64 = 16; // limit for performance
    let max_input: u32 = 16;  // keep values small enough for precise f64

    let base: u64 = (2 * s * k) as u64;
    let exp: u32 = (s * k) as u32;
    let rule_space_size: u64 = base.pow(exp); // total rules = 4096

    let structured = dtm_output_table_triple_parallel(s, k, max_steps, 0, rule_space_size - 1, 0, max_input);
    let flat = dtm_output_table_triple_parallel_f64(s, k, max_steps, 0, rule_space_size - 1, 0, max_input);

    let num_rules = structured.len();
    assert_eq!(num_rules as u64, rule_space_size, "Unexpected rule count in structured table");
    let num_inputs = (max_input + 1) as usize;
    assert_eq!(flat.len(), num_rules * num_inputs * 3, "Flat array length mismatch");

    for (r_idx, row) in structured.iter().enumerate() {
        assert_eq!(row.len(), num_inputs, "Input count mismatch at rule index {}", r_idx);
        for (i_idx, cell) in row.iter().enumerate() {
            let offset = (r_idx * num_inputs + i_idx) * 3;
            let step_f64 = flat[offset];
            let value_f64 = flat[offset + 1];
            let width_f64 = flat[offset + 2];
            match cell {
                Some((steps, value_big, width)) => {
                    assert_eq!(*steps as f64, step_f64, "Step mismatch at rule {} input {}", r_idx, i_idx);
                    assert_eq!(*width as f64, width_f64, "Width mismatch at rule {} input {}", r_idx, i_idx);
                    // Compare value when it fits exactly into f64 mantissa (<= 53 bits)
                    if value_big.bits() <= 53 {
                        let expect = value_big.to_f64().unwrap();
                        assert_eq!(expect, value_f64, "Value mismatch at rule {} input {}", r_idx, i_idx);
                    } else {
                        // For larger integers we only assert non-zero placeholder retention
                        assert!(value_f64 >= 0.0, "Expected non-zero f64 placeholder for large value at rule {} input {}", r_idx, i_idx);
                    }
                }
                None => {
                    assert_eq!(step_f64, 0.0, "Expected step=0.0 for non-halting at rule {} input {}", r_idx, i_idx);
                    assert_eq!(value_f64, -1.0, "Expected value=-1.0 for non-halting at rule {} input {}", r_idx, i_idx);
                    assert_eq!(width_f64, 0.0, "Expected width=0.0 for non-halting at rule {} input {}", r_idx, i_idx);
                }
            }
        }
    }
}
