
BeginPackage["TuringMachineSearch`"]

OneSidedTuringMachineMultiwayGraph
TagPathToEdgePath
MultiwayTuringMachineFoldList


Begin["`Private`"]

EncodeInput[n_, k_Integer : 2] := With[{digits = IntegerDigits[n, Max[k, 2]]},
    {{1, Length[digits], -1}, {digits, 0}}
]

DecodeState[{{_, _, shift_}, tape : {__Integer}}, k_Integer : 2] := 
    If[ shift == 0,
        FromDigits[Most[tape], k],
        FromDigits[tape, k]
    ]

DecodeState[{{head_, pos_, shift_}, {tape : {__Integer}, _}}, k_Integer : 2] :=
    DecodeState[{{head, pos, shift}, tape}, k]
                

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
    "ReturnTargetSubgraph" -> False,
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
    inits, layers, g, coords, nonHaltVertices
},
    inits = EncodeInput[#, k] & /@ Flatten[{input}];
    g = ResourceFunction["NestGraphTagged"][
        state |-> If[state[[1, 1, 3]] == 0, {}, # -> TuringMachine[#][state[[1]]] -> state[[2]] + 1 & /@ ruleCases],
        MapIndexed[#1 -> #2[[1]] &, inits],
        steps
	];
    layers = VertexList[g][[All, 2]];
    g = VertexReplace[g, (state_ -> _) :> CanonicalState[state]];
    inits = CanonicalState /@ inits;
    If[ TrueQ[OptionValue["UniqueValue"]],
        g = VertexReplace[g, {{_, p_, 0}, t_} :> {{1, p, 0}, t}]
    ];

    If[ TrueQ[OptionValue["EdgeDeduplication"]],
        g = EdgeDelete[g, Keys @ Select[Counts[EdgeList[g]], # > 1 &]]
    ];

    nonHaltVertices = Cases[Pick[VertexList[g], VertexOutDegree[g], 0], {{_, _, Except[0]}, _}];
    g = EdgeAdd[g, MapIndexed[#1 -> #2[[1]] &, nonHaltVertices]];
    coords = GraphEmbedding[FindSpanningTree[g], {
        "LayeredDigraphEmbedding",
        "RootVertex" -> First[VertexList[g]],
        "VertexLayerPosition" -> - Join[layers, ConstantArray[Max[layers] + 1, Length[nonHaltVertices]]]
    }];
    g = Graph[
        g,
        FilterRules[{opts}, Options[Graph]],
        VertexLabels -> {
            state : Except[_Integer] :> Which[
                state[[1, 3]] == 0,
                Placed[Style[DecodeState[state, k], OptionValue["OutputLabelStyle"]], Below],
                MemberQ[inits, state],
                Placed[Style[DecodeState[state, k], OptionValue["InputLabelStyle"]], Above],
                True,
                Replace[OptionValue["IntermediateLabelStyle"],
                    style : Except[None] :> Placed[Style[DecodeState[state, k], style], {Bottom, Left}]
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
	    VertexSize -> {"Scaled", .01},
        VertexCoordinates -> coords,
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
        TuringMachineRuleCases[{#, s, k}] & /@ rules,
        input,
        steps,
        FilterRules[{opts}, Options[OneSidedTuringMachineMultiwayGraph]]
    ],
    ruleIndex = First /@ PositionIndex[rules],
    paths = OneSidedMultiwayTuringMachineSearch[{rules, s, k}, input, #, steps] & /@
        Flatten[{Replace[targets, None -> {}]}]
}, {
    sg = If[MatchQ[targets, _Integer],
        Subgraph[g, TagPathToEdgePath[g, Lookup[ruleIndex, paths[[1]]]]],
        Subgraph[g, TagPathToEdgePath[g, Lookup[ruleIndex, #]]] & /@ paths
    ]
},
    If[ TrueQ[OptionValue["ReturnTargetSubgraph"]],
        sg,
        HighlightGraph[g, sg,
            FilterRules[{opts}, GraphHighlightStyle]
        ]
    ]
]

OneSidedTuringMachineMultiwayGraph[rules_List, args___] :=
    OneSidedTuringMachineMultiwayGraph[TuringMachineRuleCases /@ rules, args]


TagPathToEdgePath[g_ ? GraphQ, tagPath_, init_ : Automatic] /; VertexCount[g] > 0 :=
	FoldPairList[
		With[{edge = First[EdgeList[g, DirectedEdge[#1, _, #2 | {_, #2}]], Missing[#2]]},
			{edge, edge[[2]]}
        ] &,
		Replace[init, Automatic :> SelectFirst[VertexList[g], VertexInDegree[g, #] == 0 &, First[VertexList[g]]]],
		tagPath
	]


MultiwayTuringMachineFoldList[{rules : {___Integer}, _Integer, k_Integer}, input_Integer] :=
    Prepend[input] @ FoldPairList[
        {DecodeState[#1, k], If[#1[[1, 3]] == 0, #1, TuringMachine[#2][#1]]} &,
        EncodeInput[input, k],
        Thread[rules]
    ]



End[]
EndPackage[]
