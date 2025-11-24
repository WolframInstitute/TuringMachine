
BeginPackage["TuringMachineSearch`Visualizations`"]

OneSidedTuringMachinePlot::usage = 
  "OneSidedTuringMachinePlot[rule, input, maxsteps, opts] generates a visualization of the evolution of a one-sided Turing machine.
   - rule: an integer encoding the Turing machine rules.
   - input: an integer representing the binary input on the tape.
   - maxsteps: the maximum number of steps to simulate.
   Options:
   - \"Width\": the width of the tape to display (default: \"Maximum\").
   - \"Input\": the input value to label the plot (default: Automatic).
   - \"LabelInput\": whether to label the input value (default: False).
   - \"LabelOutput\": whether to label the output value (default: True).
   - \"PlotSize\": the size of the plot (default: \"Automatic\").
   - \"UndefinedLabel\": the label to use if the output is undefined (default: Undefined).
   - \"LabelInputStyle\": style options for the input label (default: {}).
   - \"LabelOutputStyle\": style options for the output label (default: {}).
   - \"TerminationColumnColor\": color for the termination column (default: GrayLevel[.7]).
   - ImageSize: size of the image (default: 50)."


Begin["`Private`"]


EncodeInput[n_, maxsteps_ : 5] := {{1, maxsteps + 1, 0}, Join[IntegerDigits[n , 2, maxsteps + 1], {0}]}

DecodeInput[{headstate_, tape_}] := FromDigits[Most[tape]]

CalculateOutput[{headstate_, tape_}, OptionsPattern[{"UndefinedValue" -> Undefined}]] := 
    If[headstate[[2]] != Length[tape], OptionValue["UndefinedValue"], FromDigits[ Most[tape], 2]] 

CalculateOutput[s_String, OptionsPattern[{"UndefinedValue" -> Undefined}]] := CalculateOutput[ToExpression[s]] 


Options[OneSidedTuringMachinePlot] = Join[{
    "Width" -> "Maximum", 
    "Input" -> Automatic,
    "LabelInput" -> False,
    "LabelOutput" -> True, 
    "PlotSize" -> "Automatic",
    "UndefinedLabel" -> Undefined, 
    "LabelInputStyle" -> {},
    "LabelOutputStyle" -> {}, 
    "TerminationColumnColor" -> GrayLevel[.7],
    ImageSize -> 50
}, Options[ArrayPlot]]

OneSidedTuringMachinePlot[rule_, input_Integer, maxsteps_Integer, opts : OptionsPattern[]] := 
    OneSidedTuringMachinePlot[rule, input, {maxsteps, "Maximum"}, opts]

OneSidedTuringMachinePlot[rule_, input_Integer, {maxsteps_Integer, width_}, opts : OptionsPattern[]] := Block[{
    t = 0, states
},
    states = NestWhileList[
        (t++; TuringMachine[rule, #]) &,
        EncodeInput[input, maxsteps],
        #[[1, 2]] <= maxsteps + 1 &,
        1,
        maxsteps
    ];
    OneSidedTuringMachinePlot[states, "Width" -> width, "Input" -> input, opts]
]

OneSidedTuringMachinePlot[states_List, opts : OptionsPattern[]] := With[{
    wval = If[# === "Maximum", Length[states[[1, -1]]] - 1, #] &[OptionValue["Width"]]
}, {
    leftcut = Length[states[[1, -1]]] - wval,
    labelInputQ = TrueQ[OptionValue["LabelInput"]],
    labelOutputQ = TrueQ[OptionValue["LabelOutput"]]
},
   ArrayPlot[
        MapAt[-1 &, Last[#][[leftcut ;;]] & /@ states, {All, -1}], 
        FilterRules[FilterRules[{opts}, Options[ArrayPlot]], Except[ImageSize]], 
        ImageSize -> Replace[OptionValue[ImageSize], {
            s_Integer :> {s / 10, s / 12} * {wval, Length[states]},
            {w_, f_ /; Head[f] === Function} :> {w, f[Length[states]]}
        }],
        Mesh -> True,
        AspectRatio -> Full,
        ColorRules -> {
            0 -> GrayLevel[1], 
            1 -> RGBColor[0.965, 0.401, 0.18], 
            2 -> RGBColor[0.977, 0.952, 0.], -1 -> 
            OptionValue["TerminationColumnColor"]
        },
        Epilog -> With[{
            headpoints = CompressedData["1:eJxTTMoPSmViYGAQBmIQ7WAMAoftGaAAzr/gcuPDl11w8QNnQOAOQT5U/36Yfjgf1fz9DAvuf8+PW7J/QfOCxaG6B/czSNj3Vn/evP8Av0OWsPru/QwCENoBKt4AUwfVx4BmLgOqufYwPlS/PUw/1Hx7mPlQ++1h9sP9D7UHPXwABXFyYA=="],
            headstates = states[[All, 1, 1]]
        }, {
            s = Max[headstates], 
            origin = headpoints[[13]]
        }, {
            headangles = Most[Subdivide[2 Pi , s]]
        },  
            Join[
                {Black}, 
                MapThread[
                    Function[{coord, headstate}, 
                        FilledCurve[
                            BezierCurve[
                                RotationTransform[headangles[[headstate]], coord] /@ (# + coord & /@ headpoints)
                            ]
                        ]
                    ],
                    {Transpose[{states[[All, 1, 2]] - 1/2 - leftcut + 1, 1/2 + Length[states] - Range[Length[states]]}],  headstates}
                ]
            ]
        ]
    ] //
    If[ labelInputQ || labelOutputQ, 
        Labeled[#,
            {
                If[ labelInputQ,
                    Style[Text[If[# === Automatic, DecodeInput[First[states]], #] &[OptionValue["Input"]]], 10, OptionValue["LabelInputStyle"]],
                    None
                ], 
                If[ labelOutputQ,
                    Style[Text[CalculateOutput[Last[states], "UndefinedValue" -> OptionValue["UndefinedLabel"]]], 10, OptionValue["LabelOutputStyle"]],
                    None
                ]
            } // DeleteCases[None]
            ,
            If[ labelInputQ, 
                If[labelOutputQ, {Top, Bottom}, {Top}], {Bottom}
            ]
            , 
            FrameMargins -> {{Automatic, Automatic}, {Automatic, None}}
        ] &,
        Identity
    ]
]

End[]

EndPackage[]