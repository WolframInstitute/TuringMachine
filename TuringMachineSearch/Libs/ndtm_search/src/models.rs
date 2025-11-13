use bit_vec::BitVec;
use num_bigint::{BigInt, BigUint};
// HashMap no longer needed here after refactor
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
        if self.0.get(position).unwrap_or(false) {
            1
        } else {
            0
        }
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
    pub next_state: u32,
    pub write_symbol: u32,
    pub move_right: bool, // true for Right, false for Left
}

#[derive(Debug, Clone)]
pub struct TuringMachine {
    // Indexed by (state-1)*num_symbols + symbol
    pub rules: Vec<Vec<Rule>>,
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
                            println!(
                                "{{{}, {}}} -> {{{}, {}, {}}}",
                                state, symbol, rule.next_state, rule.write_symbol, dir
                            );
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
                println!(
                    "Merged TuringMachine rules for {:?}, {{{}, {}}}",
                    nums, s, k
                );
                for state in 1..=s {
                    for symbol in 0..k {
                        let rules = tm.get_rules(state, symbol);
                        if !rules.is_empty() {
                            print!("{{{}, {}}} -> {{", state, symbol);
                            let mut first = true;
                            for rule in rules {
                                if !first {
                                    print!(", ");
                                } else {
                                    first = false;
                                }
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
        let two_s_k = 2 * s * k;
        let s_k = (s * k) as usize;

        let max_n = BigInt::from(two_s_k).pow(s_k as u32) - 1;
        if *n < BigInt::from(0) || *n > max_n {
            return Err(format!(
                "Rule number out of range. Must be between 0 and {}",
                max_n
            ));
        }

        let (_sign, mut digits) = n.to_radix_be(two_s_k);
        if digits.len() < s_k {
            let pad = s_k - digits.len();
            let mut new_digits = Vec::with_capacity(s_k);
            new_digits.extend(std::iter::repeat(0).take(pad));
            new_digits.extend(digits);
            digits = new_digits;
        }

        // Deterministic TM: exactly one rule per (state, symbol). Preallocate vector capacity.
        let mut rules: Vec<Vec<Rule>> = vec![Vec::new(); s_k];

        // Assign digits in state-major, symbol-reversed-minor (high-to-low symbol order)
        // digit_index = i * k + (k - 1 - j)
        for i in 0..s {
            for j in 0..k {
                let digit_index = (i * k + (k - 1 - j)) as usize;
                let digit_val = digits[digit_index] as u32;
                // state = i+1, symbol = j (used implicitly in slot computation)
                let next_state = ((digit_val / (k * 2)) % s) + 1;
                let write_symbol = (digit_val / 2) % k;
                let move_right = (digit_val & 1) == 1;
                let rule = Rule { next_state, write_symbol, move_right };
                let slot = (i * k + j) as usize; // index for (state=current_state, symbol=read_symbol)
                rules[slot] = vec![rule];
            }
        }

        Ok(TuringMachine {
            rules,
            num_states: s,
            num_symbols: k,
        })
    }

    /// Constructs a non-deterministic TuringMachine from multiple rule numbers
    pub fn from_numbers(nums: &[BigInt], s: u32, k: u32) -> Result<Self, String> {
        let s_k = (s * k) as usize;
        let mut rules: Vec<Vec<Rule>> = vec![Vec::new(); s_k];
        for n in nums {
            let tm_single = TuringMachine::from_number(n, s, k)?;
            for state in 1..=s {
                for symbol in 0..k {
                    let idx = ((state - 1) * k + symbol) as usize;
                    // from_number guarantees exactly one rule in slot
                    if let Some(rule) = tm_single.rules[idx].get(0) {
                        rules[idx].push(*rule); // Rule is Copy
                    }
                }
            }
        }
        Ok(TuringMachine { rules, num_states: s, num_symbols: k })
    }

    /// Constructs a deterministic TuringMachine directly from a slice of rule triples.
    /// Each triple is (next_state, write_symbol, direction) where direction is 1 (right) or -1 (left).
    /// The order of triples must be state-major, symbol-minor: index = (state-1)*num_symbols + symbol
    pub fn from_rule_triples(
        triples: &[(u32, u32, i32)],
        num_states: u32,
        num_symbols: u32,
    ) -> Result<Self, String> {
        let expected = (num_states * num_symbols) as usize;
        if triples.len() != expected {
            return Err(format!(
                "Expected {} rule triples (got {}) for a deterministic TM with {} states and {} symbols",
                expected,
                triples.len(),
                num_states,
                num_symbols
            ));
        }
        let mut rules: Vec<Vec<Rule>> = vec![Vec::new(); expected];
        for (idx, (next_state, write_symbol, dir)) in triples.iter().copied().enumerate() {
            if next_state == 0 || next_state > num_states {
                return Err(format!("Invalid next_state {} at index {}", next_state, idx));
            }
            if write_symbol >= num_symbols {
                return Err(format!("Invalid write_symbol {} at index {}", write_symbol, idx));
            }
            if dir != 1 && dir != -1 {
                return Err(format!("Invalid direction {} at index {} (must be 1 or -1)", dir, idx));
            }
            let move_right = dir == 1;
            rules[idx] = vec![Rule { next_state, write_symbol, move_right }];
        }
        Ok(TuringMachine { rules, num_states, num_symbols })
    }

    pub fn get_rule(&self, state: u32, symbol: u32) -> Option<&Rule> {
        if state == 0 || state > self.num_states || symbol >= self.num_symbols { return None; }
        let idx = ((state - 1) * self.num_symbols + symbol) as usize;
        self.rules[idx].get(0)
    }

    /// Returns all possible rules for a given (state, symbol) pair
    pub fn get_rules(&self, state: u32, symbol: u32) -> Vec<Rule> {
        if state == 0 || state > self.num_states || symbol >= self.num_symbols { return Vec::new(); }
        let idx = ((state - 1) * self.num_symbols + symbol) as usize;
        self.rules[idx].clone()
    }

    /// Simulate one step of the DTM, returns (halted, new_state)
    pub fn step_dtm(&self, state: &TMState) -> (bool, TMState) {
        let mut new_state = state.clone();
        let current_symbol = new_state.tape.read(new_state.head_position);
        if let Some(rule) = self.get_rule(new_state.head_state, current_symbol) {
            new_state
                .tape
                .write(new_state.head_position, rule.write_symbol);
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
    /// In-place deterministic step: mutates state directly. Returns true if halted after this step.
    pub fn step_dtm_mut(&self, state: &mut TMState) -> bool {
        let current_symbol = state.tape.read(state.head_position);
        if let Some(rule) = self.get_rule(state.head_state, current_symbol) {
            state.tape.write(state.head_position, rule.write_symbol);
            state.head_state = rule.next_state;
            if rule.move_right {
                if state.head_position == 0 {
                    // Halting: would move off the LSB end
                    return true;
                }
                state.head_position -= 1;
            } else {
                state.head_position += 1;
            }
            false
        } else {
            true
        }
    }
    /// Non-deterministic step: returns all possible next TMState objects, rule numbers, and halting status for a given state
    pub fn ndtm_step(&self, state: &TMState) -> Vec<(TMState, u64, bool)> {
        let mut next_states = Vec::new();
        let current_symbol = state.tape.read(state.head_position);
        let rules = self.get_rules(state.head_state, current_symbol);
        for (idx, rule) in rules.into_iter().enumerate() {
            let mut new_state = state.clone();
            new_state
                .tape
                .write(new_state.head_position, rule.write_symbol);
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
            // Use index within the rule vector for this (state, symbol) as rule identifier
            next_states.push((new_state, idx as u64, halted));
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
