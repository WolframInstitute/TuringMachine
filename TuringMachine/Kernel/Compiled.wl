BeginPackage["WolframInstitute`TuringMachineSearch`"]


Begin["`Private`"];

types = {
    TypeDeclaration["Product", "TMOutput", <|
        "value" -> "MachineInteger",
        "write" -> "MachineInteger",
        "dir" -> "MachineInteger"
    |>],
    TypeDeclaration["Product", "TMRule", <|
        "value" -> "MachineInteger",
        "read" -> "MachineInteger",
        "outputs" -> "DynamicArray"::["TMOutput"]
    |>],
    TypeDeclaration["Product", "TMState", <|
        "value" -> "MachineInteger",
        "pos" -> "MachineInteger",
        "tape" -> "PackedArray"::["MachineInteger", 1]
    |>],
    TypeDeclaration["Product", "TMStateWithStep", <|
        "step" -> "MachineInteger",
        "state" -> "TMState"
    |>],
    TypeDeclaration["Macro", "TMStates", "ListVector"::["TMState"]],
    TypeDeclaration["Macro", "TMRules", "ListVector"::["TMRule"]]
};

makeTMState[value_, pos_, tape_, maxWidth_] :=
    Block[{tapeLen = Length[tape], len, newTape},
        len = If[maxWidth > 0, Max[maxWidth, tapeLen], tapeLen];
		newTape = ConstantArray[0, len];
		Do[newTape[[len + 1 - i]] = tape[[-i]], {i, tapeLen}];
        CreateTypeInstance["TMState", <|
            "value" -> value,
            "pos" -> If[maxWidth > 0, len - tapeLen + Mod[pos, tapeLen , 1], pos],
            "tape" -> newTape
        |>]
    ]

makeTMRule[value_, read_, outputs_] :=
    Block[{outputsArray = CreateDataStructure["DynamicArray"::["TMOutput"]]},
        Do[
            outputsArray["Append",
                CreateTypeInstance["TMOutput", <|"value" -> output[[1]], "write" -> output[[2]], "dir" -> output[[3]]|>]
            ],
            {output, outputs}
        ];
        CreateTypeInstance["TMRule", <|"value" -> value, "read" -> read, "outputs" -> outputsArray|>]
    ]

doTMStep[state_, rules_] :=
    Block[{
        nextStates = CreateDataStructure["DynamicArray"::["TMState"]],
        value = state["value"], pos = state["pos"], tape = state["tape"], len, read
    },
        len = Length[tape];
        pos = Mod[pos, len, 1];
        read = tape[[pos]];
        Do[
            If[ rule["value"] == value && rule["read"] == read,
                Do[
                   Block[{newState, newTape},
                       newTape = Native`Copy[tape];
                       newTape[[pos]] = output["write"];
                       newState = CreateTypeInstance["TMState", <|
                           "value" -> output["value"],
                           "pos" -> Mod[pos + output["dir"], len, 1],
                           "tape" -> newTape
                       |>];
                       nextStates["Append", newState];
                   ];
                   ,
                   {output, rule["outputs"]}
                ]
            ],
            {rule, rules}
        ];
        
        nextStates
    ]


doTMStepInfinite[state_, rules_] :=
    Block[{
        nextStates = CreateDataStructure["DynamicArray"::["TMState"]],
        value = state["value"], pos = state["pos"], tape = state["tape"], len, read
    },
        len = Length[tape];
        read = If[0 < pos <= len, tape[[pos]], 0];
        Do[
            If[ rule["value"] == value && rule["read"] == read,
                Do[
                   Block[{newState, newValue = output["value"], write = output["write"], dir = output["dir"], newPos, newTape},
                       newPos = pos + dir;
                       Which[
                           pos < 1 && write != 0,
                               newTape = Join[{write}, ConstantArray[0, - pos], tape];
                               newState = CreateTypeInstance["TMState", <|
                                   "value" -> newValue,
                                   "pos" -> 1 + dir,
                                   "tape" -> newTape
                               |>];
                           ,
                           pos > len && write != 0,
                               newTape = Join[tape, ConstantArray[0, pos - len - 1], {write}];
                               newState = CreateTypeInstance["TMState", <|
                                   "value" -> newValue,
                                   "pos" -> newPos,
                                   "tape" -> newTape
                               |>];
                           ,
                           True,
                               newTape = Native`Copy[tape];
                               If[0 < pos <= len, newTape[[pos]] = write];
                               newState = CreateTypeInstance["TMState", <|
                                   "value" -> newValue,
                                   "pos" -> newPos,
                                   "tape" -> newTape
                               |>];
                       ];
                       nextStates["Append", newState];
                   ]
                   ,
                   {output, rule["outputs"]}
                ]
            ],
            {rule, rules}
        ];
        
        nextStates
    ]

doTMStepInfiniteHalt[state_, rules_] :=
    Block[{
        nextStates = CreateDataStructure["DynamicArray"::["TMState"]],
        value = state["value"], pos = state["pos"], tape = state["tape"], len, read
    },
        len = Length[tape];
        If[ pos > len,
            Return[nextStates]
        ];
        read = If[0 < pos <= len, tape[[pos]], 0];
        Do[
            If[ rule["value"] == value && rule["read"] == read,
                Do[
                   Block[{newState, newValue = output["value"], write = output["write"], dir = output["dir"], newPos, newTape},
                       newPos = pos + dir;
                       Which[
                           pos < 1 && write != 0,
                               newTape = Join[{write}, ConstantArray[0, - pos], tape];
                               newState = CreateTypeInstance["TMState", <|
                                   "value" -> newValue,
                                   "pos" -> 1 + dir,
                                   "tape" -> newTape
                               |>];
                           ,
                           (*pos > len && write != 0,
                               newState = Join[{newValue, newPos}, state[[3 ;;]], ConstantArray[0, pos - len - 1], {write}]
                           ,*)
                           True,
                               newTape = Native`Copy[tape];
                               If[0 < pos <= len, newTape[[pos]] = write];
                               newState = CreateTypeInstance["TMState", <|
                                   "value" -> newValue,
                                   "pos" -> newPos,
                                   "tape" -> newTape
                               |>];
                       ];
                       nextStates["Append", newState];
                   ]
                   ,
                   {output, rule["outputs"]}
                ]
            ],
            {rule, rules}
        ];
        
        nextStates
    ]

doTMStepInfiniteHaltWidth[state_, rules_, maxWidth_] :=
    Block[{
        nextStates = CreateDataStructure["DynamicArray"::["TMState"]],
        value = state["value"], pos = state["pos"], tape = state["tape"], len, read
    },
        If[ pos > maxWidth || pos < 1,
            Return[nextStates]
        ];
        (* Assume position is always within bounds *)
        read = tape[[pos]];
        Do[
            If[ rule["value"] == value && rule["read"] == read,
                Do[
                   Block[{newState, newValue = output["value"], write = output["write"], dir = output["dir"], newPos, newTape},
                       newPos = pos + dir;
                       newTape = Native`Copy[tape];
                       newTape[[pos]] = write;
                       newState = CreateTypeInstance["TMState", <|
                           "value" -> newValue,
                           "pos" -> newPos,
                           "tape" -> newTape
                       |>];
                       nextStates["Append", newState]
                   ];
                   ,
                   {output, rule["outputs"]}
                ]
            ],
            {rule, rules}
        ];
        
        nextStates
    ]

doMultipleTMSteps[states_, rules_, nSteps_, maxWidth_] :=
    Block[{
        allStates = CreateDataStructure["HashSet"::["TMState"]],
        timeStates = CreateDataStructure["DynamicArray"::["TMStateWithStep"]],
        currentStates, newStates,
        do = Which[maxWidth == 0, doTMStepInfiniteHalt, maxWidth > 0, doTMStepInfiniteHaltWidth[#1, #2, maxWidth] &, True, doTMStep]
    },
        currentStates = CreateDataStructure["HashSet"::["TMState"]];
        Do[If[allStates["Insert", state], timeStates["Append", CreateTypeInstance["TMStateWithStep", <|"step" -> 0, "state" -> state|>]]], {state, states}];
        currentStates = allStates;
        Do[
            newStates = CreateDataStructure["HashSet"::["TMState"]];
            Do[
                Do[newStates["Insert", newState], {newState, do[state, rules]}],
                {state, currentStates}
            ];
            If[Length[newStates] == 0, Break[]];
            Do[If[allStates["Insert", newState], timeStates["Append", CreateTypeInstance["TMStateWithStep", <|"step" -> t, "state" -> newState|>]]], {newState, newStates}];
            currentStates = newStates;
            ,
            {t, nSteps}
        ];
        timeStates
    ]

doMultipleTMStepsSingle[state_, rules_, nSteps_, maxWidth_] :=
    Block[{
        allStates = CreateDataStructure["DynamicArray"::["TMState"]],
        currentState = state,
        do = Which[maxWidth == 0, doTMStepInfiniteHalt, maxWidth > 0, doTMStepInfiniteHaltWidth[#1, #2, maxWidth] &, True, doTMStep]
    },
        allStates["Append", currentState];
        Do[
            Do[allStates["Append", currentState = nextState], {nextState, do[currentState, rules]}];
            ,
            nSteps
        ];
        allStates
    ]

doMultipleTMStepsSingleFinal[state_, rules_, nSteps_, maxWidth_] :=
    Block[{
        currentState = state, curT = 0, states,
        do = Which[maxWidth == 0, doTMStepInfiniteHalt, maxWidth > 0, doTMStepInfiniteHaltWidth[#1, #2, maxWidth] &, True, doTMStep]
    },
        Do[
            curT = t;
            states = do[currentState, rules];
            If[Length[states] == 0, curT--; Break[]];
            currentState = First[states]
            ,
            {t, nSteps}
        ];
        CreateTypeInstance["TMStateWithStep", <|"step" -> curT, "state" -> currentState|>]
    ]

functions = {
    FunctionDeclaration[
        makeTMState,
        Typed[{"MachineInteger", "MachineInteger", "PackedArray"::["MachineInteger", 1], "MachineInteger"} -> "TMState"][
            DownValuesFunction[makeTMState]
        ]
    ],
    FunctionDeclaration[
        makeTMRule,
        Typed[{"MachineInteger", "MachineInteger", "PackedArray"::["MachineInteger", 2]} -> "TMRule"][
            DownValuesFunction[makeTMRule]
        ]
    ],
    FunctionDeclaration[
        doTMStep,
        Typed[{"TMState", "TMRules"} -> "DynamicArray"::["TMState"]][
            DownValuesFunction[doTMStep]
        ]
    ],
    FunctionDeclaration[
        doTMStepInfinite,
        Typed[{"TMState", "TMRules"} -> "DynamicArray"::["TMState"]][
            DownValuesFunction[doTMStepInfinite]
        ]
    ],
    FunctionDeclaration[
        doTMStepInfiniteHalt,
        Typed[{"TMState", "TMRules"} -> "DynamicArray"::["TMState"]][
            DownValuesFunction[doTMStepInfiniteHalt]
        ]
    ],
    FunctionDeclaration[
        doTMStepInfiniteHaltWidth,
        Typed[{"TMState", "TMRules", "MachineInteger"} -> "DynamicArray"::["TMState"]][
            DownValuesFunction[doTMStepInfiniteHaltWidth]
        ]
    ],
	FunctionDeclaration[
	    doMultipleTMSteps,
	    Typed[{"TMStates", "TMRules", "MachineInteger", "MachineInteger"} -> "DynamicArray"::["TMStateWithStep"]][
	        DownValuesFunction[doMultipleTMSteps]
	    ]
	],
	FunctionDeclaration[
	    doMultipleTMStepsSingle,
	    Typed[{"TMState", "TMRules", "MachineInteger", "MachineInteger"} -> "DynamicArray"::["TMState"]][
	        DownValuesFunction[doMultipleTMStepsSingle]
	    ]
	],
    FunctionDeclaration[
	    doMultipleTMStepsSingleFinal,
	    Typed[{"TMState", "TMRules", "MachineInteger", "MachineInteger"} -> "TMStateWithStep"][
	        DownValuesFunction[doMultipleTMStepsSingleFinal]
	    ]
	]
};

declarations = Join[types, functions];

TuringMachineStates = Function[{
		Typed[rules, "ListVector"::["ListVector"::["InertExpression"]]],
        Typed[init, "ListVector"::["InertExpression"]],
        Typed[nSteps, "MachineInteger"],
        Typed[maxWidth, "MachineInteger"]
    },
		Map[
            Function[{Typed[state, "TMState"]}, Join[{state["value"], state["pos"]}, state["tape"]]],
            doMultipleTMStepsSingle[
                makeTMState[
                    Cast[init[[1]][[1]], "MachineInteger"],
                    Cast[init[[1]][[2]], "MachineInteger"],
                    Cast[init[[2]], "PackedArray"::["MachineInteger", 1]],
                    maxWidth
                ],
                makeTMRule[
                    Cast[#[[1]], "MachineInteger"],
                    Cast[#[[2]], "MachineInteger"],
                    Cast[#[[3]], "PackedArray"::["MachineInteger", 2]]
                ] & /@ rules,
                nSteps,
                maxWidth
            ]["Elements"]
        ]
	];

TuringMachineState = Function[{
		Typed[rules, "ListVector"::["ListVector"::["InertExpression"]]],
        Typed[init, "ListVector"::["InertExpression"]],
        Typed[nSteps, "MachineInteger"],
        Typed[maxWidth, "MachineInteger"]
    },
        Block[{res},
            res = doMultipleTMStepsSingleFinal[
                makeTMState[
                    Cast[init[[1]][[1]], "MachineInteger"],
                    Cast[init[[1]][[2]], "MachineInteger"],
                    Cast[init[[2]], "PackedArray"::["MachineInteger", 1]],
                    maxWidth
                ],
                makeTMRule[
                    Cast[#[[1]], "MachineInteger"],
                    Cast[#[[2]], "MachineInteger"],
                    Cast[#[[3]], "PackedArray"::["MachineInteger", 2]]
                ] & /@ rules,
                nSteps,
                maxWidth
            ];
            Join[{res["step"], res["state"]["value"], res["state"]["pos"]}, res["state"]["tape"]]
        ]
	]

MultiwayTuringMachineStates = Function[{
		Typed[rules, "ListVector"::["ListVector"::["InertExpression"]]],
        Typed[inits, "ListVector"::["ListVector"::["InertExpression"]]],
        Typed[nSteps, "MachineInteger"],
        Typed[maxWidth, "MachineInteger"]
    },
		Map[
            Function[{Typed[res, "TMStateWithStep"]}, Join[{res["step"], res["state"]["value"], res["state"]["pos"]}, res["state"]["tape"]]],
            doMultipleTMSteps[
                makeTMState[
                    Cast[#[[1]][[1]], "MachineInteger"],
                    Cast[#[[1]][[2]], "MachineInteger"],
                    Cast[#[[2]], "PackedArray"::["MachineInteger", 1]],
                    maxWidth
                ] & /@ inits,
                makeTMRule[
                    Cast[#[[1]], "MachineInteger"],
                    Cast[#[[2]], "MachineInteger"],
                    Cast[#[[3]], "PackedArray"::["MachineInteger", 2]]
                ] & /@ rules,
                nSteps,
                maxWidth
            ]["Elements"]
        ]
	]

{TuringMachineStatesCompiled, TuringMachineStateCompiled, MultiwayTuringMachineStatesCompiled} :=
	{TuringMachineStatesCompiled, TuringMachineStateCompiled, MultiwayTuringMachineStatesCompiled} =
		FunctionCompile[declarations,
			{TuringMachineStates, TuringMachineState, MultiwayTuringMachineStates},
			TargetSystem -> All
		]

prepRules[ruleNumbers : {__Integer}] := prepRules[
	ResourceFunction["TuringMachineFromNumber"] /@ ruleNumbers
]

prepRules[rules : {__List}] := KeyValueMap[
	Append,
	GroupBy[
		Catenate[rules],
		First -> Last
	]
]

MultiwayTuringMachineNative[rules_, inits_, nSteps_, infiniteQ : _ ? BooleanQ : False] := Block[{visited = CreateDataStructure["HashSet"]},
	DeleteCases[{}] @ Association @ MapIndexed[
		#2[[1]] - 1 -> #1[[All, 2]] &,
		NestList[Select[visited["Insert", #[[2]]] &] @* Catenate @* Map[state |-> {state[[1]] + 1, MapAt[Most, 1] @ TuringMachine[#][state[[2]]]} & /@ rules], {0, If[infiniteQ, MapAt[{#, 0} &, #, {2}], #]} & /@ inits, nSteps]
	]
]

TerminatingTuringMachine[rule : _Integer | {_Integer, _Integer, _Integer}, args___] := TerminatingTuringMachine[ResourceFunction["TuringMachineFromNumber"][rule], args]

TerminatingTuringMachine[rule : {_Integer, _Integer, _Integer}, args___] := TerminatingTuringMachine[ResourceFunction["TuringMachineFromNumber"] @@ rule, args]

TerminatingTuringMachine[rule_, init_Integer, args___] := With[{digits = IntegerDigits[init, 2]},
	TerminatingTuringMachine[rule, {{1, Length[digits]}, digits}, args]
]

TerminatingTuringMachine[rules_List, init_List, maxSteps_Integer, args___] := TerminatingTuringMachine[rules, init, <|"MaxSteps" -> maxSteps|>, args]

TerminatingTuringMachine[rules_List, init_List, config_Association, "FullStates"] := With[{maxSteps = Lookup[config, "MaxSteps", 0], maxWidth = Lookup[config, "MaxWidth", 0]},
	TakeDrop[#, 2] & /@ TuringMachineStatesCompiled[prepRules[{rules}], init, maxSteps, maxWidth]
]

TerminatingTuringMachine[rules_List, init_List, config_Association] := Last /@ TerminatingTuringMachine[rules, init, config, "FullStates"]

TerminatingTuringMachine[rules_List, init_List, config_Association, "FullFinalState"] := With[{maxSteps = Lookup[config, "MaxSteps", 0], maxWidth = Lookup[config, "MaxWidth", 0]},
	TuringMachineStateCompiled[prepRules[{rules}], init, maxSteps, maxWidth]
]

TerminatingTuringMachine[rules_List, init_List, config_Association, "FinalState"] := Drop[TerminatingTuringMachine[rules, init, config, "FullFinalState"], 3]

TerminatingTuringMachine[rules_List, init_List, config_Association, "Steps"] := With[{
	t = First[TerminatingTuringMachine[rules, init, config, "FullFinalState"]]
},
	If[ t >= Lookup[config, "MaxSteps", 0],
	    Infinity,
	    t
	]
]	

TerminatingTuringMachine[rules_List, init_List, config_Association, "FinalStateAndSteps"] := 
    With[{maxSteps = Lookup[config, "MaxSteps", 0], maxWidth = Lookup[config, "MaxWidth", 0]},
        With[{result = TuringMachineStateCompiled[prepRules[{rules}], init, maxSteps, maxWidth]},
            <|"Steps" -> result[[1]], "State" -> Drop[result, 3]|>
        ]
    ]

TerminatingTuringMachine[rules_List, init_List, config_Association, "FinalFullStateAndSteps"] := 
    With[{maxSteps = Lookup[config, "MaxSteps", 0], maxWidth = Lookup[config, "MaxWidth", 0]},
        With[{result = TuringMachineStateCompiled[prepRules[{rules}], init, maxSteps, maxWidth]},
            <|"Steps" -> result[[1]], "FullState" -> TakeDrop[Drop[result, 1], 2]|>
        ]
    ]


TuringMachineFunction[rule_, init_, maxSteps_Integer, ___] := With[{state = TerminatingTuringMachine[rule, init, maxSteps, "FullFinalState"]},
	If[ state[[1]] >= maxSteps,
	    Undefined,
	    FromDigits[Drop[state, 3], 2]
	]
]

TuringMachineFunction[rule_, init_, maxSteps_Integer, True] := With[{state = TerminatingTuringMachine[rule, init, maxSteps, "FinalStateAndSteps"]},
	If[ state["Steps"] >= maxSteps,
	    {Infinity, Undefined},
	    {state["Steps"], FromDigits[state["State"], 2]}
	]
]


TerminatingMultiwayTuringMachine[rules_, inits : {__Integer}, args___] :=
	TerminatingMultiwayTuringMachine[rules, With[{digits = IntegerDigits[#, 2]}, {{1, Length[digits]}, digits}] & /@ inits, args]

TerminatingMultiwayTuringMachine[rules_, init_Integer, args___] := TerminatingMultiwayTuringMachine[rules, {init}, args]

TerminatingMultiwayTuringMachine[rules_, inits_, maxSteps_Integer] := TerminatingMultiwayTuringMachine[rules, inits, <|"MaxSteps" -> maxSteps|>]

TerminatingMultiwayTuringMachine[rules : {__Integer}, inits_, config_Association] := With[{maxSteps = Lookup[config, "MaxSteps", 0], maxWidth = Lookup[config, "MaxWidth", 0]},
	GroupBy[MultiwayTuringMachineStatesCompiled[prepRules[rules], inits, maxSteps, maxWidth], First -> (TakeDrop[Rest[#], 2] &)]
]


MultiwayTuringMachineFunction[rule_, init_, maxSteps_Integer] := With[{
    states = TerminatingMultiwayTuringMachine[rule, init, maxSteps]
},
	Map[FromDigits[#[[2]], 2] &, Select[#[[1, 2]] > Length[#[[2]]] &] /@ states, {2}]
]

End[]

EndPackage[]
