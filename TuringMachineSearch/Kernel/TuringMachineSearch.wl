BeginPackage["TuringMachineSearch`", "ExtensionCargo`"]

TuringMachineFunction::usage = "TuringMachineFunction[rule, input, maxSteps] runs the deterministic Turing machine defined by 'rule' for at most 'maxSteps' steps and returns {steps, output} if it halts, otherwise {Infinity, Undefined}."

MultiwayTuringMachineSearch::usage = "MultiwayTuringMachineSearch[rules, input, output, maxSteps] attempts to find a sequence of transitions in a non-deterministic Turing machine defined by 'rules' that transforms 'input' into 'output' within 'maxSteps' steps."

MultiwayTuringMachineFunction::usage = "MultiwayTuringMachineFunction[rules, numStates, numSymbols, input, maxSteps] traverses a non-deterministic Turing machine and returns all unique tape values from halted states."

MultiwayNonHaltedStatesLeft::usage = "MultiwayNonHaltedStatesLeft[rules, numStates, numSymbols, input, maxSteps] returns the number of non-halted states remaining in the traversal queue after exploring up to 'maxSteps' steps."

TuringMachineRules::usage = "TuringMachineRules[rule, numStates, numSymbols] returns an association mapping {state, symbol} to the transition triple {nextState, writeSymbol, direction}."

MultiwayTuringMachineRules::usage = "MultiwayTuringMachineRules[rules, numStates, numSymbols] returns an association mapping {state, symbol} to a list of transition triples {nextState, writeSymbol, direction}."

TuringMachineOutputTable::usage = "TuringMachineOutputTable[numStates, numSymbols, maxSteps, maxInput] or TuringMachineOutputTable[numStates, numSymbols, maxSteps, minInput, maxInput] returns a nested list of halted outputs for every rule number and input in the range minInput..maxInput (default minInput=0). Non-halting entries are Missing[\"NonHalting\"]."

TuringMachineOutputTableWithSteps::usage = "TuringMachineOutputTableWithSteps[numStates, numSymbols, maxSteps, maxInput] or TuringMachineOutputTableWithSteps[numStates, numSymbols, maxSteps, minInput, maxInput] returns a nested list where each cell is Missing[\"NonHalting\"] or {steps, output} for halting machines over inputs minInput..maxInput (default minInput=0)."

ClearAll["TuringMachineSearch`*", "TuringMachineSearch`**`*"]

Begin["`Private`"];

functions := functions = CargoLoad[
    PacletObject["TuringMachineSearch"],
    "Functions"
]

MultiwayTMFunctionSearchRust := functions["exhaustive_search_wl"]
MultiwayTMFunctionSearchRustParallel := functions["exhaustive_search_parallel_wl"]
CollectSeenValuesRust := functions["collect_seen_values_wl"]
CollectSeenValuesWithTargetRust := functions["collect_seen_values_with_target_wl"]
RunDeterministicTMRust := functions["run_dtm_wl"]
MultiwayQueueSizeRust := functions["ndtm_traverse_queue_size_wl"]
TuringMachineRulesRust := functions["tm_rules_from_number_wl"]
MultiwayTuringMachineRulesRust := functions["tm_rules_from_numbers_wl"]
DTMOutputTableRust := functions["dtm_output_table_parallel_wl"]
DTMOutputTableStepsRust := functions["dtm_output_table_steps_parallel_wl"]


TuringMachineFunction[rules : {{_Integer, _Integer, _Integer} ..}, numStates_Integer, numSymbols_Integer, input_Integer, maxSteps_Integer] :=
    Replace[
        RunDeterministicTMRust[
            Apply[Developer`DataStore, rules, {0, 1}],
            numStates,
            numSymbols,
            ToString[input],
            maxSteps
        ],
        _[steps_, output_] :> If[0 < steps < maxSteps, {steps, FromDigits[output]}, {Infinity, Undefined}]
    ]

TuringMachineFunction[rules : {({_Integer, _Integer} -> {_Integer, _Integer, _Integer}) ..}, input_Integer, maxSteps_Integer] :=
    TuringMachineFunction[Values[rules], Sequence @@ CountDistinct /@ Thread[Keys[rules]], input, maxSteps]

TuringMachineFunction[rule_Integer, input_Integer, maxSteps_Integer] :=
    TuringMachineFunction[{rule, 2, 2}, input, maxSteps]

TuringMachineFunction[{rule_Integer, numStates_Integer, numSymbols_Integer}, input_Integer, maxSteps_Integer] :=
    TuringMachineFunction[TuringMachineRules[rule, numStates, numSymbols][[All, 2]], numStates, numSymbols, input, maxSteps]

Options[MultiwayTuringMachineSearch] = {"Parallel" -> False}

MultiwayTuringMachineSearch[
    rules : {__Integer},
    numStates_Integer,
    numSymbols_Integer,
    input_Integer,
    output_Integer,
    maxSteps_Integer,
    OptionsPattern[]
] := Replace[
    List @@ FromDigits /@ If[TrueQ[OptionValue["Parallel"]], MultiwayTMFunctionSearchRustParallel, MultiwayTMFunctionSearchRust][
        ToString /@ Developer`DataStore @@ rules,
        numStates,
        numSymbols,
        ToString[input],
        ToString[output],
        maxSteps
    ],
    {} -> Failure["PathNotFound", <|"MessageTemplate" -> "Failed to find the target."|>]
]

MultiwayTuringMachineSearch[rules : {__Integer}, input_Integer, output_Integer, maxSteps_Integer, opts : OptionsPattern[]] :=
    MultiwayTuringMachineSearch[rules, 2, 2, input, output, maxSteps, opts]


MultiwayTuringMachineFunction[
    rules : {__Integer},
    numStates_Integer,
    numSymbols_Integer,
    input_Integer,
    config_Association
] := With[{maxSteps = Lookup[config, "MaxSteps", 1000], target = Lookup[config, "Target"]},
   List @@ MapAt[List @@@ List @@ # &, {1}] @ MapAt[FromDigits, {1, All, 2}] @ If[MissingQ[target],
        CollectSeenValuesRust[
            ToString /@ Developer`DataStore @@ rules,
            numStates,
            numSymbols,
            ToString[input],
            maxSteps
        ],
        CollectSeenValuesWithTargetRust[
            ToString /@ Developer`DataStore @@ rules,
            numStates,
            numSymbols,
            ToString[input],
            ToString[target],
            maxSteps
        ]
    ]
]

MultiwayTuringMachineFunction[rules : {__Integer}, numStates_Integer, numSymbols_Integer, input_, maxSteps_Integer] :=
    MultiwayTuringMachineFunction[rules, numStates, numSymbols, input, <|"MaxSteps" -> maxSteps|>]

MultiwayTuringMachineFunction[rules : {__Integer}, numStates_Integer, numSymbols_Integer, input_, target_, maxSteps_Integer] :=
    MultiwayTuringMachineFunction[rules, numStates, numSymbols, input, <|"MaxSteps" -> maxSteps, "Target" -> target|>]

MultiwayTuringMachineFunction[rules : {__Integer}, input_, args : Repeated[_Integer, 2]] :=
    MultiwayTuringMachineFunction[rules, 2, 2, input, args]


MultiwayNonHaltedStatesLeft[
    rules : {__Integer},
    numStates_Integer,
    numSymbols_Integer,
    input_Integer,
    maxSteps_Integer
] :=
    MultiwayQueueSizeRust[
        ToString /@ Developer`DataStore @@ rules,
        numStates,
        numSymbols,
        ToString[input],
        maxSteps
    ]

MultiwayNonHaltedStatesLeft[rules : {__Integer}, input_Integer, maxSteps_Integer] :=
    MultiwayNonHaltedStatesLeft[rules, 2, 2, input, maxSteps]


TuringMachineRules[
    rule_Integer,
    numStates_Integer,
    numSymbols_Integer
] := Rule @@@ Apply[List, TuringMachineRulesRust[ToString[rule], numStates, numSymbols], {0, 2}]

TuringMachineRules[{rule_Integer, numStates_Integer, numSymbols_Integer}] :=
    TuringMachineRules[rule, numStates, numSymbols]

MultiwayTuringMachineRules[
    rules : {__Integer},
    numStates_Integer,
    numSymbols_Integer
] := Rule @@@ Apply[List, MultiwayTuringMachineRulesRust[ToString /@ Developer`DataStore @@ rules, numStates, numSymbols], {0, 3}]

MultiwayTuringMachineRules[rules : {__Integer}] := MultiwayTuringMachineRules[rules, 2, 2]


TuringMachineOutputTable[numStates_Integer, numSymbols_Integer, maxSteps_Integer, minInput_Integer, maxInput_Integer, "Bytes"] :=
    ByteArray @ DTMOutputTableRust[numStates, numSymbols, maxSteps, minInput, maxInput]

TuringMachineOutputTable[numStates_Integer, numSymbols_Integer, maxSteps_Integer, minInput_Integer, maxInput_Integer, Automatic] :=
    BinaryDeserialize @ TuringMachineOutputTable[numStates, numSymbols, maxSteps, minInput, maxInput, "Bytes"] /. Null -> Undefined

TuringMachineOutputTable[numStates_Integer, numSymbols_Integer, maxSteps_Integer, maxInput_Integer, prop : _String | Automatic : Automatic] :=
    TuringMachineOutputTable[numStates, numSymbols, maxSteps, 0, maxInput, prop]

TuringMachineOutputTable[maxSteps_Integer, maxInput_Integer, prop : _String | Automatic : Automatic] := TuringMachineOutputTable[2, 2, maxSteps, 0, maxInput, prop]

TuringMachineOutputTable[maxSteps_Integer, minInput_Integer, maxInput_Integer, prop : _String | Automatic : Automatic] := TuringMachineOutputTable[2, 2, maxSteps, minInput, maxInput, prop]


TuringMachineOutputTableWithSteps[numStates_Integer, numSymbols_Integer, maxSteps_Integer, minInput_Integer, maxInput_Integer, "Bytes"] :=
    ByteArray @ DTMOutputTableStepsRust[numStates, numSymbols, maxSteps, minInput, maxInput]

TuringMachineOutputTableWithSteps[numStates_Integer, numSymbols_Integer, maxSteps_Integer, minInput_Integer, maxInput_Integer, Automatic] :=
    BinaryDeserialize @ TuringMachineOutputTableWithSteps[numStates, numSymbols, maxSteps, minInput, maxInput, "Bytes"] /. Null -> {Infinity, Undefined}

TuringMachineOutputTableWithSteps[numStates_Integer, numSymbols_Integer, maxSteps_Integer, maxInput_Integer, prop : _String | Automatic : Automatic] :=
    TuringMachineOutputTableWithSteps[numStates, numSymbols, maxSteps, 0, maxInput, prop]

TuringMachineOutputTableWithSteps[maxSteps_Integer, maxInput_Integer, prop : _String | Automatic : Automatic] := TuringMachineOutputTableWithSteps[2, 2, maxSteps, 0, maxInput, prop]

TuringMachineOutputTableWithSteps[maxSteps_Integer, minInput_Integer, maxInput_Integer, prop : _String | Automatic : Automatic] := TuringMachineOutputTableWithSteps[2, 2, maxSteps, minInput, maxInput, prop]


End[]

EndPackage[]
