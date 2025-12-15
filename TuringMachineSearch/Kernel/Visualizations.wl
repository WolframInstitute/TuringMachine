(* ::Package:: *)

BeginPackage["TuringMachineSearch`"]

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

OneSidedTuringMachineEvolution

Begin["`Private`"]

$PvsNPStyles = <|
    "FunctionValues" -> Darker[StandardBlue, .2], 
    "TuringMachineColorRules" -> {
        0 -> GrayLevel[1], 
        1 -> StandardOrange, 
        2 -> RGBColor[0.977, 0.952, 0.],
        -1 -> GrayLevel[.7]
    }, 
    "DistributionColor" -> Directive[{Hue[0.483, 0.6, 0.772], EdgeForm[None]}], 
    "FrameStyle" -> GrayLevel[.7], 
    "MultiwayPathColorRules" -> {
        1 -> RGBColor[0.34500000000000003`, 0.712, 1], 
        2 -> RGBColor[0.68, 0.58, 1]
    }
|>



DecodeInput[{_, tape_}, k_Integer : 2] := FromDigits[Most[tape], k]

CalculateOutput[{headstate_, tape_}, k_Integer : 2, undef_ : Undefined] := 
    If[headstate[[2]] != Length[tape], undef, FromDigits[ Most[tape], k]] 

CalculateOutput[s_String, args___] := CalculateOutput[ToExpression[s], args]



OneSidedTuringMachineEvolution[{rule_Integer, s_Integer, k_Integer}, input_Integer, maxSteps_Integer, width_ : Automatic] := With[
    {history = OneSidedTuringMachineFunction[{rule, s, k}, input, maxSteps, "History"]},
    {w = Replace[width, {Automatic :> Max[Max[history[[All, 2]]] + 1, IntegerLength[input, k] + 1], "Maximum"->maxSteps+1}]}
,
    Replace[
        history,
        {state_, pos_, value_} :> {
            {state, w - pos, 1 - pos},
            PadLeft[Append[0] @ IntegerDigits[value, k], w]
        },
        1
    ]
]

Options[OneSidedTuringMachinePlot] = Join[{
    "Width" -> Automatic,
    "HorizontalPadding" -> 1,
    "Input" -> Automatic, 
    "LabelInput" -> False, 
    "kValue" -> Automatic,
    "sValue" -> Automatic, 
    "LabelOutput"-> True, 
    "LabelRuntime" -> False, 
    "LabelRuntimeStyle" -> {},
    "PlotSize" -> "Automatic", 
    "UndefinedLabel" -> Undefined, 
    "LabelInputStyle" -> {},
    "LabelOutputStyle" -> {}, 
    "TerminationColumnColor" -> GrayLevel[.7], 
    ImageSize -> 50
},
    Options[ArrayPlot]
]

Options[OneSidedTuringMachinePlot] = 
Join[
{"Width" -> Automatic,
 "HorizontalPadding" -> 1, 
"Input" -> Automatic, 
"LabelInput" -> False,
 "kValue" -> Automatic,
"sValue" -> Automatic, "LabelOutput"-> True, 
    "LabelRuntime" -> False, 
    "LabelRuntimeStyle" -> {},
    "PlotSize" -> "Automatic", 
    "UndefinedLabel" -> Undefined, 
    "LabelInputStyle" -> {},
    "LabelOutputStyle" -> {},
 "LabelOutputFunction"-> Automatic,
    "TerminationColumnColor" -> GrayLevel[.7]},
    Options[ArrayPlot]
];

OneSidedTuringMachinePlot[rule_, input_Integer, maxsteps_Integer, opts : OptionsPattern[]] := 
    OneSidedTuringMachinePlot[rule, input, {maxsteps, Automatic}, opts]

OneSidedTuringMachinePlot[rule : {_Integer, _Integer, _Integer}, input_Integer, {maxsteps_Integer, width_}, opts : OptionsPattern[]] :=
    OneSidedTuringMachinePlot[
       OneSidedTuringMachineEvolution[rule, input, maxsteps, "Maximum"],
        "Width" -> width, "Input" -> input, "sValue" -> rule[[2]], "kValue"-> rule[[3]], opts
    ]

OneSidedTuringMachinePlot[states_List, opts : OptionsPattern[]] := 
With[{
    wval = Replace[OptionValue["Width"], {
        Automatic :> Max[
            If[ OptionValue["Input"] === Automatic,
                - Infinity,
                IntegerLength[OptionValue["Input"], OptionValue["kValue"]]
            ],
            Max[- states[[All, 1, 3]]] + 2
        ] + OptionValue["HorizontalPadding"],
        w_ ? NumericQ :> w - 1
    }],
    headstates = states[[All, 1, 1]],
    headpoints = CompressedData["1:eJxTTMoPSmViYGAQBmIQ7WAMAoftGaAAzr/gcuPDl11w8QNnQOAOQT5U/36Yfjgf1fz9DAvuf8+PW7J/QfOCxaG6B/czSNj3Vn/evP8Av0OWsPru/QwCENoBKt4AUwfVx4BmLgOqufYwPlS/PUw/1Hx7mPlQ++1h9sP9D7UHPXwABXFyYA=="]
}, {
    leftcut = Max[Length[states[[1, 2]]] - wval, 1],
    labelInputQ = TrueQ[OptionValue["LabelInput"]],
    labelOutputQ = TrueQ[OptionValue["LabelOutput"]],
labelOutputFunction = OptionValue["LabelOutputFunction"],
    s = Replace[OptionValue["sValue"], Automatic :> Max[headstates]],
    k = Replace[OptionValue["kValue"], Automatic :> Max[states[[All, 1, 3]]]]
},
   ArrayPlot[
        MapAt[-1 &, #[[2, leftcut ;;]] & /@ states, {All, -1}], 
        FilterRules[FilterRules[{opts}, Options[ArrayPlot]], Except[ImageSize]], 
        ImageSize -> With[{ar = {wval + 1, Length[states]}},  Replace[OptionValue[ImageSize], {
            scale_Integer :> scale / 10 * ar ,
            "Scaled" :> ((20 (Times @@ ar) ^ -.25) * ar),
            {"Scaled", a_} :> ((a / 2.5 (Times @@ ar) ^ -.25) * ar),
            {"Scaled", a_, b_} :> ((a / 2.5 (Times @@ ar) ^ -b) * ar),
            {w_, f_Function} :> {w, f[Length[states]]}
        }]],
        Mesh -> True,
        AspectRatio -> Full,
        ColorRules -> {
            0 -> GrayLevel[1], 
            1 -> RGBColor[0.965, 0.401, 0.18], 
            2 -> RGBColor[0.977, 0.952, 0.],
            -1 -> OptionValue["TerminationColumnColor"]
        },
        Epilog -> With[{
            headangles = Most[Subdivide[2 Pi, s]]
        },  
            Join[
                {Black}, 
                MapThread[
                    Function[{coord, headstate}, 
                        FilledCurve[
                            BezierCurve[
                                RotationTransform[- headangles[[headstate]], coord] /@ (# + coord & /@ headpoints)
                            ]
                        ]
                    ],
                    {
                        Transpose @ {
                            states[[All, 1, 2]] - 1 / 2 - leftcut + 1,
                            1 / 2 + Length[states] - Range[Length[states]]
                        }, 
                        headstates
                    }
                ]
            ]
        ]
    ] //

If[ labelInputQ || labelOutputQ, 
        Labeled[#,
            {
                If[ labelInputQ,
                    Style[Text[Replace[OptionValue["Input"], Automatic :> DecodeInput[First[states], k]]], 10, OptionValue["LabelInputStyle"]],
                    None
                ], 
                If[labelOutputFunction===Automatic, 
If[ labelOutputQ,
                    Style[Text[CalculateOutput[Last[states], k, OptionValue["UndefinedLabel"]]], 10, OptionValue["LabelOutputStyle"]],
                    None
                ], labelOutputFunction[states]]
            } // DeleteCases[None]
            ,
            If[ labelInputQ, 
                If[labelOutputQ, {Top, Bottom}, {Top}], {Bottom}
            ]
            , 
            FrameMargins -> {{Automatic, Automatic}, {Automatic, None}}
        ] &,
        Identity]
]


End[]

EndPackage[]
