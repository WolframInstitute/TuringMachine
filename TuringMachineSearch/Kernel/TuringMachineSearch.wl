BeginPackage["TuringMachineSearch`", "ExtensionCargo`"]

TuringMachineFunction::usage = "TuringMachineFunction[rule, input, maxSteps] runs the deterministic Turing machine defined by 'rule' for at most 'maxSteps' steps and returns {steps, output} if it halts, otherwise {Infinity, Undefined}."

MultiwayTuringMachineSearch::usage = "MultiwayTuringMachineSearch[rules, input, output, maxSteps] attempts to find a sequence of transitions in a non-deterministic Turing machine defined by 'rules' that transforms 'input' into 'output' within 'maxSteps' steps."

MultiwayTuringMachineFunction::usage = "MultiwayTuringMachineFunction[rules, numStates, numSymbols, input, maxSteps] traverses a non-deterministic Turing machine and returns all unique tape values from halted states."

MultiwaywayNonHaltedStatesLeft::usage = "MultiwaywayNonHaltedStatesLeft[rules, numStates, numSymbols, input, maxSteps] returns the number of non-halted states remaining in the traversal queue after exploring up to 'maxSteps' steps."

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


TuringMachineFunction[{rule_Integer, numStates_Integer, numSymbols_Integer}, input_Integer, maxSteps_Integer] :=
    Replace[
        RunDeterministicTMRust[
            ToString[rule],
            numStates,
            numSymbols,
            ToString[input],
            maxSteps
        ],
        _[steps_, output_] :> If[0 < steps < maxSteps, {steps, FromDigits[output]}, {Infinity, Undefined}]
    ]

TuringMachineFunction[rule_Integer, input_Integer, maxSteps_Integer] :=
    TuringMachineFunction[{rule, 2, 2}, input, maxSteps]


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


MultiwaywayNonHaltedStatesLeft[
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

MultiwaywayNonHaltedStatesLeft[rules : {__Integer}, input_Integer, maxSteps_Integer] :=
    MultiwaywayNonHaltedStatesLeft[rules, 2, 2, input, maxSteps]


End[]

EndPackage[]
