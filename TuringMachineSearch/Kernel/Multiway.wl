
BeginPackage["TuringMachineSearch`"]

OneSidedTuringMachineMultiwayGraph


Begin["`Private`"]

EncodeInput[n_, k_Integer : 2] := With[{digits = IntegerDigits[n, Max[k, 2]]},
    {{1, Length[digits], -1}, {digits, 0}}
]

Options[OneSidedTuringMachineMultiwayGraph] = Join[{
    "Width" -> Automatic,
    "ShowIntermediateLabels" -> False
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
    inits, g
},
    inits = EncodeInput[#, k] & /@ Flatten[{input}];
    g = ResourceFunction["NestGraphTagged"][
        state |-> If[state[[1, 3]] == 0, {}, # -> TuringMachine[#][state] & /@ ruleCases],
        inits,
        steps,
        GraphLayout -> {"LayeredDigraphEmbedding", "RootVertex" -> First[inits]},
	    FilterRules[{opts}, Options[ResourceFunction["NestGraphTagged"]]],
	    PlotRangePadding -> Scaled[.15]
	];

    Graph[
        g,
        VertexLabels -> state_ :> Which[
            state[[1, 3]] == 0,
            Placed[Style[FromDigits[state[[2, 1, ;; -2]], k], Bold], Below],
            MemberQ[inits, state],
            Placed[FromDigits[state[[2, 1]], k], Above],
            True,
            If[ TrueQ[OptionValue["ShowIntermediateLabels"]],
                Placed[FromDigits[state[[2, 1, ;; -2]], k], {Bottom, Left}],
                None
            ]
        ],
        VertexShapeFunction -> With[{w = Replace[OptionValue["Width"], Automatic :> Max[Length /@ VertexList[g][[All, 2, 1]]] + 1]},
            Function[Inset[
                OneSidedTuringMachinePlot[
                    { MapAt[If[#2[[1, 3]] == 0, Identity, Append[0]] @* First, {2}][#2] //
                        If[ OptionValue["Width"] === Automatic,
                            Identity,
                            With[{len = Length[#[[2]]]}, MapAt[# + (w - len) &, MapAt[PadLeft[#, w, 0] &, #, {2}], {1, 2}]] &
                        ]
                    },
                    "Width" -> w, "LabelOutput" -> False,
                    ImageSize -> {"Scaled", 64 * #3}, AspectRatio -> Automatic
                ],
                #1
            ]]
        ],
        VertexSize -> 1,
        PerformanceGoal -> "Quality"
    ]
]

OneSidedTuringMachineMultiwayGraph[rules : {{__Integer}, _Integer, _Integer}, args___] :=
    OneSidedTuringMachineMultiwayGraph[TuringMachineRuleCases /@ Thread[rules], args]

OneSidedTuringMachineMultiwayGraph[rules_List, args___] :=
    OneSidedTuringMachineMultiwayGraph[TuringMachineRuleCases /@ rules, args]


End[]
EndPackage[]
