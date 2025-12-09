BeginPackage["TuringMachineSearch`", "ExtensionCargo`"]

ClearAll["TuringMachineSearch`*", "TuringMachineSearch`**`*"]

TuringMachineRuleCount::usage = "TuringMachineRuleCount[numStates, numSymbols] returns the total number of distinct Turing machine rules possible with numStates states and numSymbols symbols."

OneSidedTuringMachineFunction::usage = "OneSidedTuringMachineFunction[rule, input, maxSteps] runs the deterministic Turing machine defined by rule for at most maxSteps steps and returns the output value.
OneSidedTuringMachineFunction[rule, input, maxSteps, prop] returns the specified property: \"Value\" (default), \"Steps\", \"Width\", or All.
- \"Value\": Returns the integer value of the tape.
- \"Steps\": Returns the number of steps taken.
- \"Width\": Returns the maximum width of the tape visited.
- All: Returns {steps, value, width}.
Returns {Infinity, Undefined, Infinity} (or parts thereof) if it does not halt within maxSteps."

OneSidedTuringMachineFind::usage = "OneSidedTuringMachineFind[rule, maxInput, maxSteps, {s, k}, rules] finds equivalent Turing Machine functions that run within same or less number of steps for a given rule."

MultiwayTuringMachineSearch::usage = "MultiwayTuringMachineSearch[rules, input, output, maxSteps] attempts to find a sequence of transitions in a non-deterministic Turing machine defined by a list of integer rules that transforms input into output within maxSteps steps (assumes 2 states, 2 symbols).
MultiwayTuringMachineSearch[rules, numStates, numSymbols, input, output, maxSteps] allows specifying the number of states and symbols."

MultiwayTuringMachineFunction::usage = "MultiwayTuringMachineFunction[rules, input, maxSteps] traverses a non-deterministic Turing machine defined by a list of integer rules and returns all unique tape values from halted states (assumes 2 states, 2 symbols).
MultiwayTuringMachineFunction[rules, numStates, numSymbols, input, maxSteps] allows specifying the number of states and symbols.
MultiwayTuringMachineFunction[rules, numStates, numSymbols, input, target, maxSteps] stops early if the target output is found."

MultiwayNonHaltedStatesLeft::usage = "MultiwayNonHaltedStatesLeft[rules, input, maxSteps] returns the number of non-halted states remaining in the traversal queue after exploring up to maxSteps steps (assumes 2 states, 2 symbols).
MultiwayNonHaltedStatesLeft[rules, numStates, numSymbols, input, maxSteps] allows specifying the number of states and symbols."

TuringMachineRuleCases::usage = "TuringMachineRuleCases[{rule, numStates, numSymbols}] returns an association mapping {state, symbol} to the transition triple {nextState, writeSymbol, direction}."

MultiwayTuringMachineRules::usage = "MultiwayTuringMachineRules[rules, numStates, numSymbols] returns an association mapping {state, symbol} to a list of transition triples {nextState, writeSymbol, direction}.
MultiwayTuringMachineRules[rules] assumes 2 states and 2 symbols."

TuringMachineOutput::usage = "TuringMachineOutput[numStates, numSymbols, maxSteps, maxInput] or TuringMachineOutput[numStates, numSymbols, maxSteps, minInput, maxInput] returns a nested list of halted outputs for every rule number and input in the range minInput..maxInput (default minInput=0). Non-halting entries are Missing[\"NonHalting\"]."

TuringMachineOutputWithSteps::usage = "TuringMachineOutputWithSteps[numStates, numSymbols, maxSteps, maxInput] or TuringMachineOutputWithSteps[numStates, numSymbols, maxSteps, minInput, maxInput] returns a nested list where each cell is Missing[\"NonHalting\"] or {steps, output} for halting machines over inputs minInput..maxInput (default minInput=0)."

TuringMachineWidths::usage = "TuringMachineWidths[numStates, numSymbols, maxSteps, maxInput] or TuringMachineWidths[numStates, numSymbols, maxSteps, minInput, maxInput] returns a matrix of maximum head widths (max absolute head position reached) for halting deterministic machines; non-halting entries are 0."

TuringMachineStepsWidths::usage = "TuringMachineStepsWidths[numStates, numSymbols, maxSteps, maxInput] returns a list of {steps, width} pairs for halting machines."

TuringMachineOutputWithStepsWidthsFloat::usage = "TuringMachineOutputWithStepsWidthsFloat[numStates, numSymbols, maxSteps, minInput, maxInput] returns a 3D numeric array of shape {rules, inputs, 3} with triples {steps, value, width}; non-halting entries are {0.0, -1.0, 0.0}."

TuringMachineSteps::usage = "TuringMachineSteps[numStates, numSymbols, maxSteps, maxInput] returns a matrix of step counts for halting machines."

TuringMachineOutputWithStepsWidths::usage = "TuringMachineOutputWithStepsWidths[numStates, numSymbols, maxSteps, maxInput] returns a nested list of {steps, output, width} for halting machines."

TuringMachineOutputWithStepsFloat::usage = "TuringMachineOutputWithStepsFloat[numStates, numSymbols, maxSteps, maxInput] returns a 3D numeric array of {steps, output}."

TuringMachineOutputWithStepsWidthsFloat::usage = "TuringMachineOutputWithStepsWidthsFloat[numStates, numSymbols, maxSteps, maxInput] returns a 3D numeric array of {steps, output, width}."

NonTerminatingTuringMachineQ::usage = "NonTerminatingTuringMachineQ[rules, input, maxSteps] returns True if the machine defined by integer rules enters a cycle within maxSteps (assumes 2 states, 2 symbols).
NonTerminatingTuringMachineQ[rules, numStates, numSymbols, input, maxSteps] allows specifying the number of states and symbols.
NonTerminatingTuringMachineQ[{rule, numStates, numSymbols}, input, maxSteps] checks a specific deterministic rule."


Begin["`Private`"];

functions := functions = Association @ KeyValueMap[
    #1 -> Composition[
        Replace[LibraryFunctionError[error_, code_] :>
            Failure["RustError", <|
                "MessageTemplate" -> "Rust error: `` (``)",
                "MessageParameters" -> {error, code},
                "Error" -> error, "ErrorCode" -> code, "Function" -> #1
            |>]
        ],
        #2
    ] &
    ,
    Replace[
        CargoLoad[
            PacletObject["TuringMachineSearch"],
            "Functions"
        ],
        _ ? FailureQ :> Replace[
            CargoBuild[PacletObject["TuringMachineSearch"]], {
                f_ ? FailureQ :> Function @ Function @ f,
                files_ :> CargoLoad[
                    files,
                    "Functions"
                ]
            }
        ]
    ]
]

MultiwayTMFunctionSearchRust := functions["exhaustive_search_wl"]
MultiwayTMFunctionSearchRustParallel := functions["exhaustive_search_parallel_wl"]
CollectSeenValuesRust := functions["collect_seen_values_wl"]
CollectSeenValuesWithTargetRust := functions["collect_seen_values_with_target_wl"]
CollectSeenValuesTuplesRust := functions["collect_seen_values_tuples_wl"]
CollectSeenValuesWithTargetTuplesRust := functions["collect_seen_values_with_target_tuples_wl"]
CollectSeenValuesTuplesInferredRust := functions["collect_seen_values_tuples_inferred_wl"]
CollectSeenValuesWithTargetTuplesInferredRust := functions["collect_seen_values_with_target_tuples_inferred_wl"]
CollectSeenValuesTriplesRust := functions["collect_seen_values_triples_wl"]
CollectSeenValuesWithTargetTriplesRust := functions["collect_seen_values_with_target_triples_wl"]
RunDeterministicTMRust := functions["run_dtm_wl"]
RunDeterministicTMWithHistoryRust := functions["run_dtm_with_history_wl"]
MultiwayQueueSizeRust := functions["ndtm_traverse_queue_size_wl"]
TuringMachineRulesRust := functions["tm_rules_from_number_wl"]
MultiwayTuringMachineRulesRust := functions["tm_rules_from_numbers_wl"]
DTMOutputTableValueRust := functions["dtm_output_table_parallel_wl"]
DTMOutputTableStepsRust := functions["dtm_output_table_parallel_steps_u64_wl"]
DTMOutputTableWidthRust := functions["dtm_output_table_parallel_width_u64_wl"]
DTMOutputTableStepsWidthRust := functions["dtm_output_table_parallel_steps_width_u64_wl"]
DTMOutputTableTripleRust := functions["dtm_output_table_triple_parallel_wl"]
DTMOutputTableFloatPairRust := functions["dtm_output_table_pair_parallel_f64_wl"]
DTMOutputTableFloatTripleRust := functions["dtm_output_table_triple_parallel_f64_wl"]
DTMOutputTableTripleWithHistoryRust := functions["dtm_output_table_triple_with_history_wl"]
DTMOutputTableTripleWithHistoryParallelRust := functions["dtm_output_table_triple_with_history_parallel_wl"]
DetectCycleRust := functions["detect_cycle_wl"]

(* Vec-based function bindings *)
DTMOutputTableValueVecRust := functions["dtm_output_table_parallel_vec_wl"]
DTMOutputTableTripleVecRust := functions["dtm_output_table_triple_parallel_vec_wl"]
DTMOutputTableStepsVecRust := functions["dtm_output_table_parallel_steps_u64_vec_wl"]
DTMOutputTableWidthVecRust := functions["dtm_output_table_parallel_width_u64_vec_wl"]
DTMOutputTableStepsWidthVecRust := functions["dtm_output_table_parallel_steps_width_u64_vec_wl"]
DTMOutputTableFloatPairVecRust := functions["dtm_output_table_pair_parallel_f64_vec_wl"]
DTMOutputTableFloatTripleVecRust := functions["dtm_output_table_triple_parallel_f64_vec_wl"]
DTMOutputTableTripleWithHistoryVecRust := functions["dtm_output_table_triple_with_history_parallel_vec_wl"]


TuringMachineRuleCount[s_Integer, k_Integer] := (2 s k) ^ (s k)


OneSidedTuringMachineFunctionNative[
    rules : {{_Integer, _Integer, _Integer} ..} |
        {{({_Integer, _Integer} -> {_Integer, _Integer, _Integer}) ..} ..},
    {minInput_Integer, maxInput_Integer},
    maxSteps_Integer,
    prop : _String | All : "Value"
] := Enclose @ With[{
    k = First @ ConfirmBy[Replace[rules, {{_, _, k_} :> k, cases_ :> Max[cases[[All, 1, 2]]] + 1}, 1], Apply[Equal]]
},
    {
    states = Table[
        With[{digits = IntegerDigits[i, k]}, {init = {{1, Length[digits], -1}, {digits, 0}}},
            NestWhileList[Apply[{TuringMachine[rule][#1], #2 + 1, Max[#3, - #1[[1, 3]]]} &], {init, 0, 1}, #[[1, 1, 3]] < 0 &, 1, maxSteps]
        ],
        {rule, rules},
        {i, minInput, maxInput}
    ]
}, {
    finalStates = Replace[
        states[[All, All, -1]],
        {state_, steps_, maxWidth_} :> If[state[[1, 3]] == 0,
            {steps, FromDigits[state[[2, 1, ;; -2]], k], maxWidth},
            {Infinity, Undefined, Infinity}
        ],
        {3}
    ]
},
    Switch[prop,
        "Steps", finalStates[[All, All, 1]],
        "Value", finalStates[[All, All, 2]],
        "MaxWidth" | "Width", finalStates[[All, All, 3]],
        "StepsWidth", finalStates[[All, All, {1, 3}]],
        "Pair", finalStates[[All, All, ;; 2]],
        All | "Array" | "Triple", finalStates,
        "History" | "Evolution" | "EvolutionHistory",
            Map[{#[[1, 1]], - #[[1, 3]], FromDigits[#[[2, 1, If[#[[1, 3]] == 0, ;; -2, All]]], k]} &, states[[All, All, All, 1]], {3}],
        _, Return[$Failed]
    ]
]

OneSidedTuringMachineFunctionNative[{All, numStates_Integer, numSymbols_Integer}, args__] :=
    OneSidedTuringMachineFunctionNative[
        {#, numStates, numSymbols} & /@ Range[0, TuringMachineRuleCount[numStates, numSymbols] - 1],
        args
    ]

OneSidedTuringMachineFunctionNative[rule : {_Integer, _Integer, _Integer}, args___] :=
    Enclose @ First @ Confirm @ OneSidedTuringMachineFunctionNative[{rule}, args]

OneSidedTuringMachineFunctionNative[rules_List, input_Integer, args___] :=
    Enclose[First /@ Confirm @ OneSidedTuringMachineFunctionNative[rules, {input, input}, args]]


Options[OneSidedTuringMachineFunction] = {Method -> "External"}

ResourceFunction["AddCodeCompletion"]["OneSidedTuringMachineFunction"][
    None, None, None, {"Value", "Steps", "Width", "StepsWidth", "Pair", "Array", "Triple", "RawValue", "RawSteps", "RawWidth", "RawStepsWidth", "History"}
]

functionSelect[prop : _String | All : "Value"] := Switch[prop,
    "Value", TuringMachineOutput,
    "RawValue", RawTuringMachineOutput,
    "Steps", TuringMachineSteps,
    "RawSteps", RawTuringMachineSteps,
    "MaxWidth" | "Width", TuringMachineWidths,
    "RawMaxWidth" | "RawWidth", RawTuringMachineWidths,
    "StepsWidth", TuringMachineStepsWidths,
    "RawStepsWidth", RawTuringMachineStepsWidths,
    "Pair", TuringMachineOutputWithStepsFloat,
    "Array" | "Triple", TuringMachineOutputWithStepsWidthsFloat,
    "History" | "Evolution" | "EvolutionHistory", TuringMachineEvolution,
    All, TuringMachineOutputWithStepsWidths,
    _, Missing[prop]
]

OneSidedTuringMachineFunction[
    {rules : {{_Integer, _Integer, _Integer} ..}, numStates_Integer, numSymbols_Integer},
    input_Integer,
    maxSteps_Integer,
    prop : _String | All : "Value",
    OptionsPattern[]
] :=
    Enclose @ Switch[OptionValue[Method],
        "External",
        If[ MatchQ[prop, "History" | "Evolution" | "EvolutionHistory"],
            List @@ Replace[
                Confirm @ RunDeterministicTMWithHistoryRust[
                    Apply[Developer`DataStore, rules, {0, 1}],
                    numStates,
                    numSymbols,
                    ToString[input],
                    maxSteps
                ],
                _[state_, pos_, value_] :> {state, pos, FromDigits[value]},
                1
            ],
            Replace[
                Confirm @ RunDeterministicTMRust[
                    Apply[Developer`DataStore, rules, {0, 1}],
                    numStates,
                    numSymbols,
                    ToString[input],
                    maxSteps
                ],
                _[steps_, output_, width_] :> If[0 < steps < maxSteps,
                    Switch[prop,
                        "Steps" | "RawSteps", steps,
                        "Value", FromDigits[output], "RawValue", output,
                        "MaxWidth" | "Width" | "RawMaxWidth", width,
                        "StepsWidth" | "RawStepsWidth", {steps, width},
                        All, {steps, FromDigits[output], width}
                    ],
                    Switch[prop,
                        "Steps", Infinity, "RawSteps", steps,
                        "Value", Undefined, "RawValue", output,
                        "MaxWidth" | "Width", Infinity, "RawMaxWidth" | "RawWidth", width,
                        "StepsWidth", {Infinity, Infinity}, "RawStepsWidth", {steps, width},
                        All, {Infinity, Undefined, Infinity}
                    ]
                ]
            ]
        ],
        "Native",
            With[{lhs = Confirm[TuringMachineRuleCases[{0, numStates, numSymbols}]][[All, 1]]},
                First @ Confirm @ OneSidedTuringMachineFunctionNative[{Thread[lhs -> rules]}, input, maxSteps, prop]
            ],
        _,
        Undefined
    ]

OneSidedTuringMachineFunction[rules : {({_Integer, _Integer} -> {_Integer, _Integer, _Integer}) ..}, input_Integer, maxSteps_Integer, prop : _String | All : "Value", opts : OptionsPattern[]] :=
    OneSidedTuringMachineFunction[{Values[rules], Splice[CountDistinct /@ Thread[Keys[rules]]]}, input, maxSteps, prop, opts]

OneSidedTuringMachineFunction[{rule_Integer, numStates_Integer, numSymbols_Integer}, input_Integer, maxSteps_Integer, prop : "Pair" | "Triple", opts : OptionsPattern[]] :=
    Enclose @ First @ Confirm @ OneSidedTuringMachineFunction[{rule, numStates, numSymbols}, {input, input}, maxSteps, prop, opts]

OneSidedTuringMachineFunction[{rule_Integer, numStates_Integer, numSymbols_Integer}, input_Integer, maxSteps_Integer, prop : _String | All : "Value", opts : OptionsPattern[]] :=
    Enclose @ OneSidedTuringMachineFunction[{Confirm[TuringMachineRuleCases[{rule, numStates, numSymbols}]][[All, 2]], numStates, numSymbols}, input, maxSteps, prop, opts]

OneSidedTuringMachineFunction[rule_Integer, input : _Integer | {_Integer, _Integer}, maxSteps_Integer, prop : _String | All : "Value", opts : OptionsPattern[]] :=
    OneSidedTuringMachineFunction[{rule, 2, 2}, input, maxSteps, prop]

OneSidedTuringMachineFunction[{rule_Integer, numStates_Integer, numSymbols_Integer}, {minInput_Integer, maxInput_Integer}, maxSteps_Integer, prop : _String | All : "Value", OptionsPattern[]] :=
    Switch[OptionValue[Method],
        "External",
            With[{f = functionSelect[prop]},
                f[rule, numStates, numSymbols, maxSteps, minInput ;; maxInput]
            ],
        "Native",
            OneSidedTuringMachineFunctionNative[{rule, numStates, numSymbols}, {minInput, maxInput}, maxSteps, prop],
        _,
            Undefined
        ]

OneSidedTuringMachineFunction[{All, numStates_Integer, numSymbols_Integer}, input : _Integer | {_Integer, _Integer}, maxSteps_Integer, prop : _String | All, OptionsPattern[]] :=
    Switch[
        OptionValue[Method],
        "External",
            With[{f = functionSelect[prop]},
                If[ MatchQ[input, _Integer],
                    f[numStates, numSymbols, maxSteps, input ;; input][[All, 1]],
                    f[numStates, numSymbols, maxSteps, Span @@ input]
                ]
            ]
        ,
        "Native",
            OneSidedTuringMachineFunctionNative[{All, numStates, numSymbols}, input, maxSteps, prop],
        _,
            Undefined
    ]

(* Vec-based patterns for explicit list of rule numbers *)
OneSidedTuringMachineFunction[{rules : {__Integer}, numStates_Integer, numSymbols_Integer}, input : _Integer | {_Integer, _Integer}, maxSteps_Integer, prop : _String | All : "Value", OptionsPattern[]] :=
    With[{f = functionSelect[prop]},
        If[ MatchQ[input, _Integer],
            f[rules, numStates, numSymbols, maxSteps, input ;; input][[All, 1]],
            f[rules, numStates, numSymbols, maxSteps, Span @@ input]
        ]
    ]

OneSidedTuringMachineFunction[{rules : {__Integer}, numStates_Integer, numSymbols_Integer}, minInput_Integer ;; maxInput_Integer, maxSteps_Integer, prop : _String | All : "Value", OptionsPattern[]] :=
    With[{f = functionSelect[prop]},
        f[rules, numStates, numSymbols, maxSteps, minInput ;; maxInput]
    ]

OneSidedTuringMachineFunction[rule_, input_, maxSteps_, opts : OptionsPattern[]] := 
    OneSidedTuringMachineFunction[rule, input, maxSteps, "Value", opts]



OneSidedTuringMachineFind[
	rule : _Integer | {Repeated[_Integer, {3}]},
	maxInput_Integer,
	maxSteps_Integer,
	args___
] := OneSidedTuringMachineFind[
	MapThread[
		Prepend,
		{
			OneSidedTuringMachineFunction[rule, {1, maxInput}, maxSteps, All][[All, ;; 2]],
			Range[maxInput]
		}
	],
	args
]
OneSidedTuringMachineFind[
	inputStepValues : {{_Integer, _Integer, _Integer} ..},
	sk : {_Integer, _Integer} : {2, 2},
	defaultRules : {___Integer} | All : All
] := Block[{
	rulesLeft,
	initRules = Replace[defaultRules, All :> Range[TuringMachineRuleCount @@ sk]],
	curInput = None
},
	Progress`EvaluateWithProgress[
		FoldWhile[{rules, x} |->
			MapThread[
				If[#2 =!= Undefined && #2 == x[[3]], #1, Nothing] &,
				{rules, OneSidedTuringMachineFunction[{rules, Splice[sk]}, curInput = x[[1]], x[[2]]]}
			],
			initRules,
			inputStepValues,
			((rulesLeft = Length[#]); # =!= {}) &
		],
		<|
			"Text" :> StringTemplate["Rules left to check: ``"][rulesLeft],
			"Detail" :> If[curInput === None, None, StringTemplate["Current input: ``"][curInput]],
			"Progress" -> Automatic,
			"Percentage" :> 1 - rulesLeft / Length[initRules]
        |>
	]
]

OneSidedTuringMachineFindFaster[___] := {}


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
] := Enclose @ With[{maxSteps = Lookup[config, "MaxSteps", 1000], target = Lookup[config, "Target"], cycleTerminateQ = Lookup[config, "CycleTerminate", False]},
   Apply[List, #, {0, 2}] & @ MapAt[FromDigits, {1, All, 2}] @ Confirm @ If[MissingQ[target],
        CollectSeenValuesRust[
            ToString /@ Developer`DataStore @@ rules,
            numStates,
            numSymbols,
            ToString[input],
            maxSteps,
            cycleTerminateQ
        ],
        CollectSeenValuesWithTargetRust[
            ToString /@ Developer`DataStore @@ rules,
            numStates,
            numSymbols,
            ToString[input],
            ToString[target],
            maxSteps,
            cycleTerminateQ
        ]
    ]
]

MultiwayTuringMachineFunction[
    rules : {({_Integer, _Integer} -> {{_Integer, _Integer, _Integer} ..}) ..},
    input_Integer,
    config_Association
] := Enclose @ With[{maxSteps = Lookup[config, "MaxSteps", 1000], target = Lookup[config, "Target"], cycleTerminateQ = Lookup[config, "CycleTerminate", False], 
    tupleRules = Apply[Developer`DataStore,
        Catenate[
            KeyValueMap[
                Function[{key, values}, 
                    Map[Join[key, #] &, values]
                ],
                Association[rules]
            ]
        ],
        {0, 1}
    ]
},
    Apply[List, #, {0, 2}] & @ MapAt[FromDigits, {1, All, 2}] @ Confirm @ If[MissingQ[target],
        CollectSeenValuesTuplesInferredRust[
            tupleRules,
            ToString[input],
            maxSteps,
            cycleTerminateQ
        ],
        CollectSeenValuesWithTargetTuplesInferredRust[
            tupleRules,
            ToString[input],
            ToString[target],
            maxSteps,
            cycleTerminateQ
        ]
    ]
]

MultiwayTuringMachineFunction[
    rules : {{_Integer, _Integer, _Integer} ..},
    numStates_Integer,
    numSymbols_Integer,
    input_Integer,
    config_Association
] := Enclose @ With[{maxSteps = Lookup[config, "MaxSteps", 1000], target = Lookup[config, "Target"], cycleTerminateQ = Lookup[config, "CycleTerminate", False]},
   Apply[List, #, {0, 2}] & @ MapAt[FromDigits, {1, All, 2}] @ Confirm @ If[MissingQ[target],
        CollectSeenValuesTriplesRust[
            rules,
            numStates,
            numSymbols,
            ToString[input],
            maxSteps,
            cycleTerminateQ
        ],
        CollectSeenValuesWithTargetTriplesRust[
            rules,
            numStates,
            numSymbols,
            ToString[input],
            ToString[target],
            maxSteps,
            cycleTerminateQ
        ]
    ]
]

MultiwayTuringMachineFunction[rules : {({_Integer, _Integer} -> {{_Integer, _Integer, _Integer} ..}) ..}, input_, maxSteps_Integer, cycleTerminateQ : _ ? BooleanQ : False] :=
    MultiwayTuringMachineFunction[rules, input, <|"MaxSteps" -> maxSteps, "CycleTerminate" -> cycleTerminateQ|>]

MultiwayTuringMachineFunction[rules : {({_Integer, _Integer} -> {{_Integer, _Integer, _Integer} ..}) ..}, input_, target_, maxSteps_Integer, cycleTerminateQ : _ ? BooleanQ : False] :=
    MultiwayTuringMachineFunction[rules, input, <|"MaxSteps" -> maxSteps, "Target" -> target, "CycleTerminate" -> cycleTerminateQ|>]

MultiwayTuringMachineFunction[rules : {__Integer} | {({_Integer, _Integer} -> {{_Integer, _Integer, _Integer} ..}) ..} | {{_Integer, _Integer, _Integer} ..}, numStates_Integer, numSymbols_Integer, input_, maxSteps_Integer, cycleTerminateQ : _ ? BooleanQ : False] :=
    MultiwayTuringMachineFunction[rules, numStates, numSymbols, input, <|"MaxSteps" -> maxSteps, "CycleTerminate" -> cycleTerminateQ|>]

MultiwayTuringMachineFunction[rules : {__Integer} | {({_Integer, _Integer} -> {{_Integer, _Integer, _Integer} ..}) ..} | {{_Integer, _Integer, _Integer} ..}, numStates_Integer, numSymbols_Integer, input_, target_, maxSteps_Integer, cycleTerminateQ : _ ? BooleanQ : False] :=
    MultiwayTuringMachineFunction[rules, numStates, numSymbols, input, <|"MaxSteps" -> maxSteps, "Target" -> target, "CycleTerminate" -> cycleTerminateQ|>]

MultiwayTuringMachineFunction[rules : {__Integer}, input_, maxSteps_Integer, cycleTerminateQ : _ ? BooleanQ : False] :=
    MultiwayTuringMachineFunction[rules, 2, 2, input, maxSteps, cycleTerminateQ]


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


NonTerminatingTuringMachineQ[
    rules : {__Integer},
    numStates_Integer,
    numSymbols_Integer,
    input_Integer,
    maxSteps_Integer
] :=
    DetectCycleRust[
        ToString /@ Developer`DataStore @@ rules,
        numStates,
        numSymbols,
        ToString[input],
        maxSteps
    ]

NonTerminatingTuringMachineQ[rules : {__Integer}, input_Integer, maxSteps_Integer] :=
    NonTerminatingTuringMachineQ[rules, 2, 2, input, maxSteps]

NonTerminatingTuringMachineQ[{rule_Integer, numStates_Integer, numSymbols_Integer}, input_Integer, maxSteps_Integer] :=
    NonTerminatingTuringMachineQ[{rule}, numStates, numSymbols, input, maxSteps]

NonTerminatingTuringMachineQ[rule_Integer, input_Integer, maxSteps_Integer] :=
    NonTerminatingTuringMachineQ[{rule}, 2, 2, input, maxSteps]

TuringMachineRuleCases[
    rule_Integer,
    numStates_Integer,
    numSymbols_Integer
] := Enclose[Rule @@@ Apply[List, Confirm @ TuringMachineRulesRust[ToString[rule], numStates, numSymbols], {0, 2}]]

TuringMachineRuleCases[{rule_Integer, numStates_Integer, numSymbols_Integer}] :=
    TuringMachineRuleCases[rule, numStates, numSymbols]

TuringMachineRuleCases[rules : {__Integer}, numStates_Integer, numSymbols_Integer] :=
    Enclose @ Normal @ GroupBy[Catenate[Confirm @ TuringMachineRuleCases[{#, numStates, numSymbols}] & /@ rules], First -> Values, DeleteDuplicates]

TuringMachineRuleCases[rule_Integer] := TuringMachineRuleCases[rule, 2, 2]

TuringMachineRuleCases[rules : {__Integer}] := TuringMachineRuleCases[rules, 2, 2]

MultiwayTuringMachineRules[
    rules : {__Integer},
    numStates_Integer,
    numSymbols_Integer
] := Enclose[
    Rule @@@ Apply[List, Confirm @ MultiwayTuringMachineRulesRust[ToString /@ Developer`DataStore @@ rules, numStates, numSymbols], {0, 3}]
]

MultiwayTuringMachineRules[rules : {__Integer}] := MultiwayTuringMachineRules[rules, 2, 2]


MapApply[Function[{f, fRust, fVecRust, import, none, subst},
    f[minRule_Integer ;; maxRule_Integer, numStates_Integer, numSymbols_Integer, maxSteps_Integer, minInput_Integer ;; maxInput_Integer, "Raw"] :=
        fRust[numStates, numSymbols, maxSteps, minRule, maxRule, minInput, maxInput];

    f[minRule_Integer ;; maxRule_Integer, numStates_Integer, numSymbols_Integer, maxSteps_Integer, minInput_Integer ;; maxInput_Integer, ___] :=
        If[subst === Inherited, Identity, ReplaceAll[none -> subst]] @ import @ f[minRule ;; maxRule, numStates, numSymbols, maxSteps, minInput ;; maxInput, "Raw"];

    f[numStates_Integer, numSymbols_Integer, maxSteps_Integer, maxInput_Integer, prop : _String | Automatic : Automatic] :=
        f[numStates, numSymbols, maxSteps, 1 ;; maxInput, prop];

    f[maxSteps_Integer, maxInput_Integer, prop : _String | Automatic : Automatic] :=
        f[2, 2, maxSteps, maxInput, prop];

    f[maxSteps_Integer, minInput_Integer ;; maxInput_Integer, prop : _String | Automatic : Automatic] :=
        f[2, 2, maxSteps, minInput ;; maxInput, prop];
    
    f[rules : _Integer | (_Integer ;; _Integer), maxSteps_Integer, minInput_Integer ;; maxInput_Integer, prop : _String | Automatic : Automatic] :=
        f[rules, 2, 2, maxSteps, minInput ;; maxInput, prop];

    f[numStates_Integer, numSymbols_Integer, maxSteps_Integer, minInput_Integer ;; maxInput_Integer, prop : _String | Automatic : Automatic] := With[
        {minRule = 0, maxRule = (2 * numStates * numSymbols) ^ (numStates * numSymbols) - 1},
        f[minRule ;; maxRule, numStates, numSymbols, maxSteps, minInput ;; maxInput, prop]
    ];

    f[rules : _Integer ;; _Integer, args__, minInput_Integer ;; maxInput_Integer, prop : _String | Automatic : Automatic] :=
        If[prop === Automatic, Map[First], Identity] @ f[rules, args, minInput ;; maxInput, prop];

    f[rule_Integer, numStates_Integer, numSymbols_Integer, maxSteps_Integer, maxInput_Integer, prop : _String | Automatic : Automatic] :=
        f[rule, numStates, numSymbols, maxSteps, 1 ;; maxInput, prop];

    f[rule_Integer, numStates_Integer, numSymbols_Integer, maxSteps_Integer, minInput_Integer ;; maxInput_Integer, prop : _String | Automatic : Automatic] :=
        If[prop === Automatic, First, Identity] @ f[rule ;; rule, numStates, numSymbols, maxSteps, minInput ;; maxInput, prop];

    (* Vec-based patterns: explicit list of rules with range of inputs using Span *)
    f[rules : {__Integer}, numStates_Integer, numSymbols_Integer, maxSteps_Integer, minInput_Integer ;; maxInput_Integer, "Raw"] :=
        fVecRust[numStates, numSymbols, maxSteps, ToString /@ Developer`DataStore @@ rules, ToString /@ Developer`DataStore @@ Range[minInput, maxInput]];

    f[rules : {__Integer}, numStates_Integer, numSymbols_Integer, maxSteps_Integer, minInput_Integer ;; maxInput_Integer, ___] :=
        If[subst === Inherited, Identity, ReplaceAll[none -> subst]] @ import @ f[rules, numStates, numSymbols, maxSteps, minInput ;; maxInput, "Raw"];

    (* Vec-based patterns: range of rules with explicit list of inputs using Span *)
    f[minRule_Integer ;; maxRule_Integer, numStates_Integer, numSymbols_Integer, maxSteps_Integer, inputs : {__Integer}, "Raw"] :=
        fVecRust[numStates, numSymbols, maxSteps, ToString /@ Developer`DataStore @@ Range[minRule, maxRule], ToString /@ Developer`DataStore @@ inputs];

    f[minRule_Integer ;; maxRule_Integer, numStates_Integer, numSymbols_Integer, maxSteps_Integer, inputs : {__Integer}, ___] :=
        If[subst === Inherited, Identity, ReplaceAll[none -> subst]] @ import @ f[minRule ;; maxRule, numStates, numSymbols, maxSteps, inputs, "Raw"];

    (* Vec-based patterns: explicit list of both rules and inputs *)
    f[rules : {__Integer}, numStates_Integer, numSymbols_Integer, maxSteps_Integer, inputs : {__Integer}, "Raw"] :=
        fVecRust[numStates, numSymbols, maxSteps, ToString /@ Developer`DataStore @@ rules, ToString /@ Developer`DataStore @@ inputs];

    f[rules : {__Integer}, numStates_Integer, numSymbols_Integer, maxSteps_Integer, inputs : {__Integer}, ___] :=
        If[subst === Inherited, Identity, ReplaceAll[none -> subst]] @ import @ f[rules, numStates, numSymbols, maxSteps, inputs, "Raw"];

    (* Convenience: vec rules with default 2,2 states/symbols *)
    f[rules : {__Integer}, maxSteps_Integer, minInput_Integer ;; maxInput_Integer, prop : _String | Automatic : Automatic] :=
        f[rules, 2, 2, maxSteps, minInput ;; maxInput, prop];

    f[rules : {__Integer}, maxSteps_Integer, inputs : {__Integer}, prop : _String | Automatic : Automatic] :=
        f[rules, 2, 2, maxSteps, inputs, prop];
    ,
    HoldAll
]
    ,
    Unevaluated @ {
        {TuringMachineOutput, DTMOutputTableValueRust, DTMOutputTableValueVecRust, BinaryDeserialize @* ByteArray, None, Undefined},
        {TuringMachineSteps, DTMOutputTableStepsRust, DTMOutputTableStepsVecRust, Normal, 0, Infinity},
        {TuringMachineWidths, DTMOutputTableWidthRust, DTMOutputTableWidthVecRust, Normal, 0, Infinity},
        {TuringMachineStepsWidths, DTMOutputTableStepsWidthRust, DTMOutputTableStepsWidthVecRust, Normal, {0, _}, {Infinity, Infinity}},
        {RawTuringMachineOutput, DTMOutputTableValueRust, DTMOutputTableValueVecRust, BinaryDeserialize @* ByteArray, None, Inherited},
        {RawTuringMachineSteps, DTMOutputTableStepsRust, DTMOutputTableStepsVecRust, Normal, 0, Inherited},
        {RawTuringMachineWidths, DTMOutputTableWidthRust, DTMOutputTableWidthVecRust, Normal, 0, Inherited},
        {RawTuringMachineStepsWidths, DTMOutputTableStepsWidthRust, DTMOutputTableStepsWidthVecRust, Normal, {0, _}, Inherited},
        {TuringMachineOutputWithStepsWidths, DTMOutputTableTripleRust, DTMOutputTableTripleVecRust, BinaryDeserialize @* ByteArray, None, {Infinity, Undefined, Infinity}},
        {TuringMachineOutputWithStepsFloat, DTMOutputTableFloatPairRust, DTMOutputTableFloatPairVecRust, Normal, None, Inherited},
        {TuringMachineOutputWithStepsWidthsFloat, DTMOutputTableFloatTripleRust, DTMOutputTableFloatTripleVecRust, Normal, None, Inherited},
        {TuringMachineEvolution, DTMOutputTableTripleWithHistoryParallelRust, DTMOutputTableTripleWithHistoryVecRust, BinaryDeserialize @* ByteArray, None, Inherited}
    }
]



End[]

EndPackage[]
