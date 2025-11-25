use bit_vec::BitVec;
use num_bigint::{BigInt, BigUint};
use std::hash::{Hash, Hasher};

/// Represents the tape of the Turing machine.
/// Binary variant uses BitVec for k=2 (optimized).
/// General variant uses Vec<u8> for k>2, storing both data and the number of symbols.
#[derive(Clone, Debug, Eq)]
pub enum Tape {
    Binary(BitVec),
    General(Vec<u8>, u32), // (data, num_symbols)
}

impl Tape {
    /// Creates a new binary tape from an integer (k=2).
    pub fn from_integer(n: &BigUint) -> Self {
        Self::from_integer_base(n, 2)
    }

    /// Creates a new tape from an integer with a specified base (number of symbols).
    pub fn from_integer_base(n: &BigUint, k: u32) -> Self {
        if k == 2 {
            // Binary optimization
            if n == &BigUint::from(0u32) {
                return Tape::Binary(BitVec::from_elem(1, false));
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
            Tape::Binary(bv)
        } else {
            // General k-ary representation
            if n == &BigUint::from(0u32) {
                return Tape::General(vec![0], k);
            }
            let mut data = Vec::new();
            let mut num = n.clone();
            let base = BigUint::from(k);
            while num > BigUint::from(0u32) {
                let digit = (&num % &base).to_u32_digits();
                data.push(if digit.is_empty() { 0 } else { digit[0] as u8 });
                num /= &base;
            }
            // Ensure at least one digit
            if data.is_empty() {
                data.push(0);
            }
            Tape::General(data, k)
        }
    }

    /// Converts the tape back to an integer.
    pub fn to_integer(&self) -> BigUint {
        match self {
            Tape::Binary(bv) => {
                let mut bytes = vec![0u8; (bv.len() + 7) / 8];
                for (i, bit) in bv.iter().enumerate() {
                    if bit {
                        let byte_index = i / 8;
                        let bit_index = i % 8;
                        bytes[byte_index] |= 1 << bit_index;
                    }
                }
                BigUint::from_bytes_le(&bytes)
            }
            Tape::General(data, k) => {
                let mut result = BigUint::from(0u32);
                let base = BigUint::from(*k);
                for (i, &digit) in data.iter().enumerate() {
                    result += BigUint::from(digit) * base.pow(i as u32);
                }
                result
            }
        }
    }

    /// Reads the symbol at the given position.
    pub fn read(&self, position: usize) -> u32 {
        match self {
            Tape::Binary(bv) => {
                if bv.get(position).unwrap_or(false) {
                    1
                } else {
                    0
                }
            }
            Tape::General(data, _k) => {
                if position < data.len() {
                    data[position] as u32
                } else {
                    0 // Default blank symbol
                }
            }
        }
    }

    /// Writes a symbol at the given position, extending the tape if necessary.
    pub fn write(&mut self, position: usize, value: u32) {
        match self {
            Tape::Binary(bv) => {
                let bool_val = value != 0;
                if position >= bv.len() {
                    bv.grow(position - bv.len() + 1, false);
                }
                bv.set(position, bool_val);
            }
            Tape::General(data, k) => {
                assert!(value < *k, "Symbol {} out of range for k={}", value, k);
                if position >= data.len() {
                    data.resize(position + 1, 0);
                }
                data[position] = value as u8;
            }
        }
    }

    /// Returns the length of the tape.
    pub fn len(&self) -> usize {
        match self {
            Tape::Binary(bv) => bv.len(),
            Tape::General(data, _k) => data.len(),
        }
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
    // Indexed by (state-1)*num_symbols + symbol.
    // For nondeterministic machines each slot is a Vec<Option<Rule>>.
    // Duplicate rules for a slot are stored as None to preserve index positions
    // without recomputing identical TMState transitions.
    pub rules: Vec<Vec<Option<Rule>>>,
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
                            for opt_rule in rules {
                                if let Some(rule) = opt_rule {
                                    if !first { print!(", "); } else { first = false; }
                                    let dir = if rule.move_right { 1 } else { -1 };
                                    print!("{{{}, {}, {}}}", rule.next_state, rule.write_symbol, dir);
                                }
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
        let mut rules: Vec<Vec<Option<Rule>>> = vec![Vec::new(); s_k];

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
                rules[slot] = vec![Some(rule)];
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
        let mut rules: Vec<Vec<Option<Rule>>> = vec![Vec::new(); s_k];
        for n in nums {
            let tm_single = TuringMachine::from_number(n, s, k)?;
            for state in 1..=s {
                for symbol in 0..k {
                    let idx = ((state - 1) * k + symbol) as usize;
                    // from_number guarantees exactly one Some(rule) in slot
                    if let Some(Some(rule)) = tm_single.rules[idx].get(0) {
                        // Check if this rule already exists (ignore None placeholders)
                        let exists = rules[idx].iter().any(|opt| opt.as_ref() == Some(rule));
                        if exists {
                            // store None placeholder to maintain index consistency
                            rules[idx].push(None);
                        } else {
                            rules[idx].push(Some(*rule));
                        }
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
        let mut rules: Vec<Vec<Option<Rule>>> = vec![Vec::new(); expected];
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
            rules[idx] = vec![Some(Rule { next_state, write_symbol, move_right })];
        }
        Ok(TuringMachine { rules, num_states, num_symbols })
    }

    /// Constructs a non-deterministic TuringMachine from a list of explicit rule tuples.
    /// Each tuple is (state, symbol, next_state, write_symbol, direction).
    pub fn from_rule_tuples(
        tuples: &[(u32, u32, u32, u32, i32)],
        num_states: u32,
        num_symbols: u32,
    ) -> Result<Self, String> {
        let s_k = (num_states * num_symbols) as usize;
        let mut rules: Vec<Vec<Option<Rule>>> = vec![Vec::new(); s_k];
        
        for (idx, (state, symbol, next_state, write_symbol, dir)) in tuples.iter().copied().enumerate() {
            if state == 0 || state > num_states {
                return Err(format!("Invalid state {} at index {}", state, idx));
            }
            if symbol >= num_symbols {
                return Err(format!("Invalid symbol {} at index {}", symbol, idx));
            }
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
            let rule = Rule { next_state, write_symbol, move_right };
            let slot = ((state - 1) * num_symbols + symbol) as usize;
            
            // Check for duplicates to avoid redundancy
            let exists = rules[slot].iter().any(|opt| opt.as_ref() == Some(&rule));
            if !exists {
                rules[slot].push(Some(rule));
            }
        }
        
        Ok(TuringMachine { rules, num_states, num_symbols })
    }

    pub fn from_rule_tuples_inferred(
        tuples: &[(u32, u32, u32, u32, i32)],
    ) -> Result<Self, String> {
        let mut max_state = 0;
        let mut max_symbol = 0;
        for (state, symbol, next_state, write_symbol, _) in tuples.iter().copied() {
            if state > max_state { max_state = state; }
            if next_state > max_state { max_state = next_state; }
            if symbol > max_symbol { max_symbol = symbol; }
            if write_symbol > max_symbol { max_symbol = write_symbol; }
        }
        // Symbols are 0-indexed, so count is max + 1
        Self::from_rule_tuples(tuples, max_state, max_symbol + 1)
    }

    pub fn from_rule_triples_inferred(
        _triples: &[(u32, u32, i32)],
    ) -> Result<Self, String> {
        // For triples, we can't infer the input state/symbol directly from the triple itself because
        // the triple is (next_state, write_symbol, direction) and its index implies the input state/symbol.
        // However, if we assume standard ordering (state-major, symbol-minor), we can try to infer.
        // But usually triples are provided for a specific s,k.
        // If the user provides a flat list of triples, they MUST match s*k.
        // We can try to factor the length.
        // But simpler: just assume 2,2 if not provided? Or try to find s,k such that s*k = len.
        // But there might be multiple factors.
        // Actually, the user request "same for rust functions" implies explicit tuples should infer.
        // For triples (dense DTM), inference is ambiguous without s,k unless we assume s=2 or something.
        // Let's stick to tuples for inference.
        // But wait, if the user provides triples, they are usually for a specific machine.
        // If the user provides `{{1,1,1}, ...}` as a list of triples, we don't know s,k.
        // Let's just implement tuple inference for now as that's unambiguous.
        Err("Inference not supported for triples (ambiguous dimensions)".to_string())
    }

    pub fn get_rule(&self, state: u32, symbol: u32) -> Option<&Rule> {
        if state == 0 || state > self.num_states || symbol >= self.num_symbols { return None; }
        let idx = ((state - 1) * self.num_symbols + symbol) as usize;
        // deterministic case: first Some
        self.rules[idx].iter().find_map(|opt| opt.as_ref())
    }

    /// Returns all possible rules for a given (state, symbol) pair
    pub fn get_rules(&self, state: u32, symbol: u32) -> Vec<Option<Rule>> {
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
        for (idx, opt_rule) in rules.into_iter().enumerate() {
            if let Some(rule) = opt_rule {
                let mut new_state = state.clone();
                new_state.tape.write(new_state.head_position, rule.write_symbol);
                new_state.head_state = rule.next_state;
                let mut halted = false;
                if rule.move_right {
                    if new_state.head_position == 0 {
                        halted = true;
                    } else {
                        new_state.head_position -= 1;
                    }
                } else {
                    new_state.head_position += 1;
                }
                next_states.push((new_state, idx as u64, halted));
            } else {
                // None placeholder: skip computation, index preserved
                continue;
            }
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
