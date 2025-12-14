
BeginPackage["TuringMachineSearch`"]

OneSidedTuringMachineMultiwayGraph

Begin["`Private`"]

EncodeInput[n_, k_Integer : 2] := With[{digits = IntegerDigits[n, k]},
    {{1, Length[digits], -1}, {digits, 0}}
]


Options[OneSidedTuringMachineMultiwayGraph] = Join[{"Width" -> Automatic}, Options[ResourceFunction["NestGraphTagged"]]];


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
        VertexLabels -> state_ :> Placed[If[
            state[[1, 3]] == 0,
            Framed[FromDigits[state[[2, 1, ;; -2]], k], Background -> Red],
            FromDigits[state[[2, 1]], k]
        ], Below],
        VertexShapeFunction -> With[{w = Replace[OptionValue["Width"], Automatic :> Max[Length /@ VertexList[g][[All, 2, 1]]] + 1]},
            Function[Inset[Framed[
                OneSidedTuringMachinePlot[
                    {MapAt[If[#2[[1, 3]] == 0, Identity, Append[0]] @* First, {2}] @ #2},
                    "LabelOutput" -> False,
                    ImageSize -> 16 * w, AspectRatio -> Automatic
                ], Background -> LightBlue, FrameMargins -> 1 / 2],
                #1, #3
            ]]
        ]
    ]
]

OneSidedTuringMachineMultiwayGraph[rules_List, args___] :=
    OneSidedTuringMachineMultiwayGraph[TuringMachineRuleCases /@ rules, args]


End[]
EndPackage[]
