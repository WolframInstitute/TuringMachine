BeginPackage["TuringMachineSearch`", "ExtensionCargo`"]

MultiwayTMFunctionSearch::usage = "MultiwayTMFunctionSearch[rules, input, output, maxSteps] attempts to find a sequence of transitions in a non-deterministic Turing machine defined by 'rules' that transforms 'input' into 'output' within 'maxSteps' steps."

CollectSeenValues::usage = "CollectSeenValues[rules, numStates, numSymbols, input, maxSteps] traverses a non-deterministic Turing machine and returns all unique tape values from halted states."

RunDeterministicTM::usage = "RunDeterministicTM[rule, input, maxSteps] runs the deterministic Turing machine defined by 'rule' for at most 'maxSteps' steps and returns {steps, output} if it halts, otherwise {Infinity, Undefined}."

ClearAll["MultiwayTMFunctionSearch`*", "MultiwayTMFunctionSearch`**`*"]

Begin["`Private`"];

functions := functions = CargoLoad[
    PacletObject["TuringMachineSearch"],
    "Functions"
]

MultiwayTMFunctionSearchRust := functions["exhaustive_search_wl"]
MultiwayTMFunctionSearchRustParallel := functions["exhaustive_search_parallel_wl"]
CollectSeenValuesRust := functions["collect_seen_values_wl"]
RunDeterministicTMRust := functions["run_dtm_wl"]

Options[MultiwayTMFunctionSearch] = {"Parallel" -> False}

MultiwayTMFunctionSearch[
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

MultiwayTMFunctionSearch[rules : {__Integer}, input_Integer, output_Integer, maxSteps_Integer, opts : OptionsPattern[]] :=
    MultiwayTMFunctionSearch[rules, 2, 2, input, output, maxSteps, opts]

CollectSeenValues[
    rules : {__Integer},
    numStates_Integer,
    numSymbols_Integer,
    input_Integer,
    maxSteps_Integer
] :=
    List @@ FromDigits /@ CollectSeenValuesRust[
        ToString /@ Developer`DataStore @@ rules,
        numStates,
        numSymbols,
        ToString[input],
        maxSteps
    ]

CollectSeenValues[rules : {__Integer}, input_Integer, maxSteps_Integer] :=
    CollectSeenValues[rules, 2, 2, input, maxSteps]

RunDeterministicTM[{rule_Integer, numStates_Integer, numSymbols_Integer}, input_Integer, maxSteps_Integer] :=
    Replace[
        RunDeterministicTMRust[
            ToString[rule],
            numStates,
            numSymbols,
            ToString[input],
            maxSteps
        ], {
            _[0, ""] -> {Infinity, Undefined},
            _[steps_, output_] :> {steps, FromDigits[output]}
        }
    ]

RunDeterministicTM[rule_Integer, input_Integer, maxSteps_Integer] := RunDeterministicTM[{rule, 2, 2}, input, maxSteps]



End[]

EndPackage[]
