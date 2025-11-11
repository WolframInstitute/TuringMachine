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

MultiwayTMFunctionSearchRust := MultiwayTMFunctionSearchRust = functions["exhaustive_search_wl"]
CollectSeenValuesRust := CollectSeenValuesRust = functions["collect_seen_values_wl"]
RunDeterministicTMRust := RunDeterministicTMRust = functions["run_dtm_wl"]

MultiwayTMFunctionSearch[
	rules : {__Integer},
    numStates_Integer,
    numSymbols_Integer,
	input_Integer,
	output_Integer,
	maxSteps_Integer
] :=
		Replace[
			List @@ MultiwayTMFunctionSearchRust[
				Developer`DataStore @@ rules,
				numStates,
				numSymbols,
				input,
				output,
				maxSteps
			],
			{} -> Failure["PathNotFound", <|"MessageTemplate" -> "Failed to find the target."|>]
		]

MultiwayTMFunctionSearch[rules : {__Integer}, input_Integer, output_Integer, maxSteps_Integer] :=
    MultiwayTMFunctionSearch[rules, 2, 2, input, output, maxSteps]

CollectSeenValues[
    rules : {__Integer},
    numStates_Integer,
    numSymbols_Integer,
    input_Integer,
    maxSteps_Integer
] :=
    List @@ CollectSeenValuesRust[
        Developer`DataStore @@ rules,
        numStates,
        numSymbols,
        input,
        maxSteps
    ]

CollectSeenValues[rules : {__Integer}, input_Integer, maxSteps_Integer] :=
    CollectSeenValues[rules, 2, 2, input, maxSteps]

RunDeterministicTM[{rule_Integer, numStates_Integer, numSymbols_Integer}, input_Integer, maxSteps_Integer] := With[{
    result = List @@ RunDeterministicTMRust[
        rule,
        numStates,
        numSymbols,
        input,
        maxSteps
    ]
},
    If[result === {}, {Infinity, Undefined}, result]
]

RunDeterministicTM[rule_Integer, input_Integer, maxSteps_Integer] := RunDeterministicTM[{rule, 2, 2}, input, maxSteps]



End[]

EndPackage[]
