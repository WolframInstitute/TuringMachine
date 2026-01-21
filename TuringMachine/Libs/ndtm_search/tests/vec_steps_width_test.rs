#![cfg(test)]
use ndtm_search::dtm_output_table_parallel_steps_width_u64_vec;
use num_bigint::{BigInt, BigUint};

#[test]
fn test_dtm_output_table_parallel_steps_width_u64_vec() {
    let s: u32 = 2;
    let k: u32 = 2;
    let max_steps: u64 = 100;
    
    let rules: Vec<BigInt> = vec![0u64, 1, 2, 3, 4].into_iter().map(BigInt::from).collect();
    let inputs: Vec<BigUint> = vec![0u32, 1, 2].into_iter().map(BigUint::from).collect();
    
    let result = dtm_output_table_parallel_steps_width_u64_vec(s, k, max_steps, &rules, &inputs);
    
    // Expected size: num_rules * num_inputs * 2 (pairs of steps, width)
    let expected_size = rules.len() * inputs.len() * 2;
    assert_eq!(result.len(), expected_size, 
        "Expected {} elements but got {}", expected_size, result.len());
    
    // Verify the array can be reshaped to [num_rules, num_inputs, 2]
    for rule_idx in 0..rules.len() {
        for input_idx in 0..inputs.len() {
            let offset = (rule_idx * inputs.len() + input_idx) * 2;
            let _steps = result[offset];
            let _width = result[offset + 1];
            // Just verify we can access without panic
        }
    }
    
    println!("Result array size: {}", result.len());
    println!("First few elements: {:?}", &result[..std::cmp::min(10, result.len())]);
}

#[test]
fn test_dtm_output_table_parallel_steps_width_u64_vec_single_element() {
    let s: u32 = 2;
    let k: u32 = 2;
    let max_steps: u64 = 100;
    
    // Single rule, single input
    let rules: Vec<BigInt> = vec![177u64].into_iter().map(BigInt::from).collect();
    let inputs: Vec<BigUint> = vec![1u32, 2].into_iter().map(BigUint::from).collect();
    
    let result = dtm_output_table_parallel_steps_width_u64_vec(s, k, max_steps, &rules, &inputs);
    
    assert_eq!(result.len(), 4, "Should have exactly 4 elements for 1 rule, 2 inputs");
    println!("Rule 177, input 1: steps={}, width={}", result[0], result[1]);
    println!("Rule 177, input 2: steps={}, width={}", result[2], result[3]);
}
