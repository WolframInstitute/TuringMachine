#![cfg(test)]
use ndtm_search::{
    dtm_output_table,
    dtm_output_table_parallel,
};

// Rust equivalent of WL snippet:
// With[{s = 2, k = 2, maxSteps = 2^9, maxInput = 2^3},
//  Table[TuringMachineFunction[rule, s, k, i, maxSteps][[2]],
//    {rule, TuringMachineRules[#, s, k][[All, 2]] & /@ Range[0, (2 s k)^(s k) - 1]}, {i, 0, maxInput}]
// ]
// Here we avoid any WL overhead and compute directly via Rust APIs.
#[test]
fn test_full_dtm_enumeration_table() {
    let s: u32 = 2;
    let k: u32 = 2;
    let max_steps: u64 = 512;
    let max_input: u32 = 1024;

    let start_native = std::time::Instant::now();
    let base: u64 = (2 * s * k) as u64;
    let exp: u32 = (s * k) as u32;
    let rule_space_size: u64 = base.pow(exp); // total rules
    let table_native = dtm_output_table(s, k, max_steps, 0, rule_space_size - 1, 0, max_input);
    let elapsed_native = start_native.elapsed();
    println!("[timing] Native table construction took {:?}", elapsed_native);

    let start_parallel = std::time::Instant::now();
    let table_parallel = dtm_output_table_parallel(s, k, max_steps, 0, rule_space_size - 1, 0, max_input);
    let elapsed_parallel = start_parallel.elapsed();
    println!("[timing] Parallel table construction took {:?}", elapsed_parallel);

    assert_eq!(table_native.len(), table_parallel.len(), "Row count mismatch");
    for (row_native, row_parallel) in table_native.iter().zip(table_parallel.iter()) {
        assert_eq!(row_native.len(), row_parallel.len(), "Column count mismatch");
        for (cell_native, cell_parallel) in row_native.iter().zip(row_parallel.iter()) {
            match (cell_native, cell_parallel) {
                (Some(a), Some(b)) => assert_eq!(a, b, "Value mismatch between serial and parallel"),
                (None, None) => {},
                _ => panic!("Halting mismatch between serial and parallel"),
            }
        }
    }
}
