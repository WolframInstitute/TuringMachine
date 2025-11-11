use clap::Parser;
use ndtm_search::exhaustive_search;
use ndtm_search::models::TuringMachine;
use num_bigint::{BigInt, BigUint};

/// Command-line arguments for the NDTM searcher.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Integers representing the Turing Machine rules.
    #[arg(short, long, required = true)]
    pub rule_nums: Vec<BigInt>,

    /// The initial integer on the tape.
    #[arg(short, long)]
    pub initial: Option<BigUint>,

    /// The target integer to find.
    #[arg(short, long)]
    pub target: Option<BigUint>,

    /// The number of states in the TM.
    #[arg(long, default_value_t = 2)]
    pub num_states: u32,

    /// The number of symbols (colors) on the tape.
    #[arg(long, default_value_t = 2)]
    pub num_symbols: u32,

    /// The maximum number of steps to search.
    #[arg(long, default_value_t = 1000)]
    pub max_steps: u32,
    /// Print the rules for the given TuringMachine and exit
    #[arg(long, default_value_t = false)]
    pub print_rules: bool,
}

fn main() {
    let args = Args::parse();

    if args.print_rules {
        TuringMachine::print_tm_rules_merged(&args.rule_nums, args.num_states, args.num_symbols);
        return;
    }

    let initial = match args.initial {
        Some(ref val) => val,
        None => {
            eprintln!("Error: --initial is required unless --print-rules is set");
            return;
        }
    };
    let target = match args.target {
        Some(ref val) => val,
        None => {
            eprintln!("Error: --target is required unless --print-rules is set");
            return;
        }
    };

    // Combine all rule numbers into a single non-deterministic TuringMachine
    let tm = match TuringMachine::from_numbers(&args.rule_nums, args.num_states, args.num_symbols) {
        Ok(tm) => tm,
        Err(e) => {
            eprintln!("Error for rules {:?}: {}", args.rule_nums, e);
            return;
        }
    };
    println!("Searching for rules {:?}...", args.rule_nums);
    match exhaustive_search(&tm, initial, target, args.max_steps) {
        Some(path) => {
            println!("Target found!");
            println!("Path: {:?}", path);
        }
        None => {
            println!("Failure: Target not found within the maximum number of steps.");
        }
    }
}
