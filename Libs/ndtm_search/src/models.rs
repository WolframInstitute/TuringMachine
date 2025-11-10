
use bit_vec::BitVec;
use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

/// Represents the tape of the Turing machine.
#[derive(Clone, Debug, Eq)]
pub struct Tape(pub BitVec);

impl Tape {
    /// Creates a new tape from an integer.
    pub fn from_integer(n: &BigUint) -> Self {
        if n == &BigUint::from(0u32) {
            return Tape(BitVec::from_elem(1, false));
        }
        let bytes = n.to_bytes_le();
        let mut bv = BitVec::new();
        for byte in bytes {
            for i in 0..8 {
                bv.push((byte >> i) & 1 == 1);
            }
        }
        // Trim leading zeros that are not part of the number's representation
        while bv.len() > 1 && !bv[bv.len() - 1] {
            bv.pop();
        }
        Tape(bv)
    }

    /// Converts the tape back to an integer.
    pub fn to_integer(&self) -> BigUint {
        let mut bytes = vec![0u8; (self.0.len() + 7) / 8];
        for (i, bit) in self.0.iter().enumerate() {
            if bit {
                let byte_index = i / 8;
                let bit_index = i % 8;
                bytes[byte_index] |= 1 << bit_index;
            }
        }
        BigUint::from_bytes_le(&bytes)
    }

    /// Reads the bit at the given position.
    pub fn read(&self, position: usize) -> u32 {
        if self.0.get(position).unwrap_or(false) { 1 } else { 0 }
    }

    /// Writes a bit at the given position, extending the tape if necessary.
    pub fn write(&mut self, position: usize, value: u32) {
        let bool_val = value != 0;
        if position >= self.0.len() {
            self.0.grow(position - self.0.len() + 1, false);
        }
        self.0.set(position, bool_val);
    }

    /// Returns the length of the tape.
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl PartialEq for Tape {
    fn eq(&self, other: &Self) -> bool {
        self.to_integer() == other.to_integer()
    }
}

impl Hash for Tape {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_integer().hash(state);
    }
}

/// Represents a transition rule for the TM.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rule {
    pub rule_number: u64,
    pub next_state: u32,
    pub write_symbol: u32,
    pub move_right: bool, // true for Right, false for Left
}

#[derive(Debug, Clone)]
pub struct TuringMachine {
    pub rules: HashMap<(u32, u32), Vec<Rule>>,
    pub num_states: u32,
    pub num_symbols: u32,
}

impl TuringMachine {
    /// Prints all rules for a given integer TuringMachine
    pub fn print_tm_rules(n: &BigInt, s: u32, k: u32) {
        match TuringMachine::from_number(n, s, k) {
            Ok(tm) => {
                println!("TuringMachine[{}, {{{}, {}}}]", n, s, k);
                for state in 1..=s {
                    for symbol in 0..k {
                        if let Some(rule) = tm.get_rule(state, symbol) {
                            let dir = if rule.move_right { 1 } else { -1 };
                            println!("{{{}, {}}} -> {{{}, {}, {}}}", state, symbol, rule.next_state, rule.write_symbol, dir);
                        }
                    }
                }
            }
            Err(e) => println!("Error: {}", e),
        }
    }
    /// Prints all merged rules for multiple integer TuringMachines in grouped format
    pub fn print_tm_rules_merged(nums: &[BigInt], s: u32, k: u32) {
        match TuringMachine::from_numbers(nums, s, k) {
            Ok(tm) => {
                println!("Merged TuringMachine rules for {:?}, {{{}, {}}}", nums, s, k);
                for state in 1..=s {
                    for symbol in 0..k {
                        let rules = tm.get_rules(state, symbol);
                        if !rules.is_empty() {
                            print!("{{{}, {}}} -> {{", state, symbol);
                            let mut first = true;
                            for rule in rules {
                                if !first { print!(", "); } else { first = false; }
                                let dir = if rule.move_right { 1 } else { -1 };
                                print!("{{{}, {}, {}}}", rule.next_state, rule.write_symbol, dir);
                            }
                            println!("}}");
                        }
                    }
                }
            }
            Err(e) => println!("Error: {}", e),
        }
    }
    pub fn from_number(n: &BigInt, s: u32, k: u32) -> Result<Self, String> {
        let two_s_k = BigInt::from(2 * s * k);
        let s_k = (s * k) as usize;

        let max_n = two_s_k.pow(s_k as u32) - 1;
        if *n < BigInt::from(0) || *n > max_n {
            return Err(format!("Rule number out of range. Must be between 0 and {}", max_n));
        }

        let (_sign, mut digits) = n.to_radix_be(2 * s * k);

        // Pad with leading zeros to get s*k digits
        while digits.len() < s_k {
            digits.insert(0, 0);
        }

        let mut rules: HashMap<(u32, u32), Vec<Rule>> = HashMap::new();
        let rule_number_u64 = n.to_u64().unwrap_or(0); // Provide a default if conversion fails

        // Assign digits in state-major, symbol-reversed-minor (high-to-low symbol order)
        // digit_index = i * k + (k - 1 - j)
        for i in 0..s { // state index
            for j in 0..k { // symbol index (reversed)
                let digit_index = (i * k + (k - 1 - j)) as usize;
                let digit = digits[digit_index];

                let current_state = (i + 1) as u32;
                let read_symbol = j as u32;

                let digit_val = digit as u32;

                // Adjusted mapping to match test expectations
                let next_state_raw = (digit_val / (k * 2)) % s;
                let write_symbol_raw = (digit_val / 2) % k;
                let move_raw = digit_val % 2;

                let next_state = next_state_raw + 1;
                let write_symbol = write_symbol_raw;
                let move_right = move_raw == 1;

                let rule = Rule { rule_number: rule_number_u64, next_state, write_symbol, move_right };
                rules.entry((current_state, read_symbol)).or_default().push(rule);
            }
        }

        Ok(TuringMachine { rules, num_states: s, num_symbols: k })
    }

    /// Constructs a non-deterministic TuringMachine from multiple rule numbers
    pub fn from_numbers(nums: &[BigInt], s: u32, k: u32) -> Result<Self, String> {
        let mut rules: HashMap<(u32, u32), Vec<Rule>> = HashMap::new();
        for n in nums {
            let tm = TuringMachine::from_number(n, s, k)?;
            for ((state, symbol), rule_vec) in tm.rules {
                rules.entry((state, symbol)).or_default().extend(rule_vec);
            }
        }
        Ok(TuringMachine { rules, num_states: s, num_symbols: k })
    }

    pub fn get_rule(&self, state: u32, symbol: u32) -> Option<&Rule> {
        self.rules.get(&(state, symbol)).and_then(|v| v.get(0))
    }

    /// Returns all possible rules for a given (state, symbol) pair
    pub fn get_rules(&self, state: u32, symbol: u32) -> Vec<Rule> {
        self.rules.get(&(state, symbol)).cloned().unwrap_or_default()
    }

    /// Simulate one step of the DTM, returns (halted, new_state)
    pub fn step_dtm(&self, state: &TMState) -> (bool, TMState) {
        let mut new_state = state.clone();
        let current_symbol = new_state.tape.read(new_state.head_position);
        if let Some(rule) = self.get_rule(new_state.head_state, current_symbol) {
            new_state.tape.write(new_state.head_position, rule.write_symbol);
            new_state.head_state = rule.next_state;
            if rule.move_right {
                // Move right (toward LSB, lower index)
                if new_state.head_position == 0 {
                    // Halt by moving off the LSB end (negative position)
                    return (true, new_state);
                }
                new_state.head_position -= 1;
            } else {
                // Move left (toward MSB, higher index)
                new_state.head_position += 1;
            }
            (false, new_state)
        } else {
            // No rule found, halt
            (true, new_state)
        }
    }
    /// Non-deterministic step: returns all possible next TMState objects, rule numbers, and halting status for a given state
    pub fn ndtm_step(&self, state: &TMState) -> Vec<(TMState, u64, bool)> {
        let mut next_states = Vec::new();
        let current_symbol = state.tape.read(state.head_position);
        let rules = self.get_rules(state.head_state, current_symbol);
        for rule in rules {
            let mut new_state = state.clone();
            new_state.tape.write(new_state.head_position, rule.write_symbol);
            new_state.head_state = rule.next_state;
            let mut halted = false;
            if rule.move_right {
                if new_state.head_position == 0 {
                    // Halting move: do not update position
                    halted = true;
                } else {
                    new_state.head_position -= 1;
                }
            } else {
                new_state.head_position += 1;
            }
            next_states.push((new_state, rule.rule_number, halted));
        }
        next_states
    }
}


/// Represents the state of the Turing Machine.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TMState {
    pub head_state: u32,
    pub head_position: usize,
    pub tape: Tape,
}

/// A node in the search space, containing a state and the path to reach it.
#[derive(Clone)]
pub struct SearchNode {
    pub state: TMState,
    pub path: Vec<u64>, // Path of rule numbers
}


