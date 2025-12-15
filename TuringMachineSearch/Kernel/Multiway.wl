
BeginPackage["TuringMachineSearch`"]

OneSidedTuringMachineMultiwayGraph
TagPathToEdgePath


Begin["`Private`"]

EncodeInput[n_, k_Integer : 2] := With[{digits = IntegerDigits[n, Max[k, 2]]},
    {{1, Length[digits], -1}, {digits, 0}}
]

CanonicalState[{{head_, pos_, shift_}, {tape : {__Integer}, _}}] := With[{nZeros = Min[LengthWhile[tape, # == 0 &], pos - 1]},
    {{head, pos - nZeros, shift}, Drop[tape, nZeros]}
]



Options[OneSidedTuringMachineMultiwayGraph] = DeleteDuplicatesBy[First] @ Join[{
    "Width" -> Automatic,
    "InputLabelStyle" -> {},
    "OutputLabelStyle" -> Bold,
    "IntermediateLabelStyle" -> None,
    "UniqueValue" -> True,
    "EdgeDeduplication" -> True,
    ColorRules -> $PvsNPStyles["MultiwayPathColorRules"],
    GraphHighlightStyle -> "Thick"
},
    Options[ResourceFunction["NestGraphTagged"]]
]


OneSidedTuringMachineMultiwayGraph[
    ruleCases : {{({_Integer, _Integer} -> {_Integer, _Integer, _Integer}) ..} ..},
    input : _Integer | {__Integer},
    steps_Integer,
    opts : OptionsPattern[]
] := Block[{
    k = Max[ruleCases[[All, All, 1, 2]]] + 1,
    inits, g, nonHaltVertices
},
    inits = EncodeInput[#, k] & /@ Flatten[{input}];
    g = ResourceFunction["NestGraphTagged"][
        state |-> If[state[[1, 3]] == 0, {}, # -> TuringMachine[#][state] & /@ ruleCases],
        inits,
        steps
	];

    g = VertexReplace[g, state_ :> CanonicalState[state]];
    inits = CanonicalState /@ inits;
    If[ TrueQ[OptionValue["UniqueValue"]],
        g = VertexReplace[g, {{_, p_, 0}, t_} :> {{1, p, 0}, t}]
    ];

    If[ TrueQ[OptionValue["EdgeDeduplication"]],
        g = EdgeDelete[g, Keys @ Select[Counts[EdgeList[g]], # > 1 &]]
    ];

    nonHaltVertices = Cases[Pick[VertexList[g], VertexOutDegree[g], 0], {{_, _, Except[0]}, _}];
    g = EdgeAdd[g, MapIndexed[#1 -> #2[[1]] &, nonHaltVertices]];
    
    g = Graph[
        g,
        FilterRules[{opts}, Options[Graph]],
        VertexLabels -> {
            state : Except[_Integer] :> Which[
                state[[1, 3]] == 0,
                Placed[Style[FromDigits[state[[2, ;; -2]], k], OptionValue["OutputLabelStyle"]], Below],
                MemberQ[inits, state],
                Placed[Style[FromDigits[state[[2]], k], OptionValue["InputLabelStyle"]], Above],
                True,
                Replace[OptionValue["IntermediateLabelStyle"],
                    style : Except[None] :> Placed[Style[FromDigits[state[[2, ;; -2]], k], style], {Bottom, Left}]
                ]
            ],
            _Integer -> None
        },
        VertexShapeFunction -> {
            With[{w = Replace[OptionValue["Width"], Automatic :> Max[Length /@ VertexList[g, Except[_Integer]][[All, 2]]] + 1]},
                Except[_Integer] -> Function[Inset[
                    Tooltip[OneSidedTuringMachinePlot[
                        { MapAt[If[#2[[1, 3]] == 0, Identity, Append[0]], {2}][#2] //
                            If[ OptionValue["Width"] === Automatic,
                                Identity,
                                With[{len = Length[#[[2]]]}, MapAt[# + (w - len) &, MapAt[PadLeft[#, w, 0] &, #, {2}], {1, 2}]] &
                            ]
                        },
                        "Width" -> w, "LabelOutput" -> False
                        ,
                        ImageSize -> {Automatic, Scaled[#3[[2]]]},
                        AspectRatio -> Automatic
                    ], #2],
                    #1
                ]]
            ],
            _Integer -> None
        },
        EdgeStyle -> {
            DirectedEdge[_, _Integer]-> StandardGray,
            DirectedEdge[_, _, {_, i_}] :> Lookup[OptionValue[ColorRules], i, None]
        },
        PlotRangePadding -> Scaled[.12],
        AspectRatio -> 1 / 1.5,
	    VertexSize -> .2,
        GraphLayout -> "LayeredDigraphEmbedding",
        PerformanceGoal -> "Quality"
    ]
]

OneSidedTuringMachineMultiwayGraph[
    {rules : {__Integer}, s_Integer, k_Integer},
    input : _Integer | {__Integer},
    steps_Integer,
    targets : _Integer | {__Integer} : None,
    opts : OptionsPattern[]
] := With[{
    g = OneSidedTuringMachineMultiwayGraph[
        TuringMachineRuleCases /@ Thread[rules],
        input,
        steps,
        FilterRules[{opts}, Options[OneSidedTuringMachineMultiwayGraph]]
    ],
    ruleIndex = First /@ PositionIndex[rules],
    paths = OneSidedMultiwayTuringMachineSearch[{rules, s, k}, input, #, steps] & /@
        Flatten[{Replace[targets, None -> {}]}]
},
    HighlightGraph[
        g,
        Subgraph[g, TagPathToEdgePath[g, Lookup[ruleIndex, #]]] & /@ paths,
        FilterRules[{opts}, GraphHighlightStyle]
    ]
]

OneSidedTuringMachineMultiwayGraph[rules_List, args___] :=
    OneSidedTuringMachineMultiwayGraph[TuringMachineRuleCases /@ rules, args]


TagPathToEdgePath[g_, rulePath_, init_ : Automatic] :=
	FoldPairList[
		With[{edge = First[EdgeList[g, DirectedEdge[#1, _, #2 | {_, #2}]]]},
			{edge, edge[[2]]}
        ] &,
		Replace[init, Automatic :> SelectFirst[VertexList[g], VertexInDegree[g, #] == 0 &, First[VertexList[g]]]],
		rulePath
	]


End[]
EndPackage[]
