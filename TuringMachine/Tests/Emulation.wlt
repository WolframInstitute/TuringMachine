(* Emulation.wlt

   The emulation functions of Kernel/Emulation.wl against the Lean
   definitions they transcribe. EmulationVectors.wl is written by
   Proofs/scripts/ExportVectors.lean, which evaluates the Lean encoders,
   evolutions and decoders on the fixtures of Proofs/Vectors/:

       cd Proofs && lake env lean scripts/ExportVectors.lean > ../TuringMachine/Tests/EmulationVectors.wl

   Run with TestReport["Tests/Emulation.wlt"] from the paclet directory. *)

PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["WolframInstitute`TuringMachine`"];
Get[FileNameJoin[{DirectoryName[$TestFileName], "EmulationVectors.wl"}]];

private = Symbol["WolframInstitute`TuringMachine`Private`" <> #] &;
missingToNone[x_] := If[MissingQ[x], None, x];

(* ::Section:: *)
(* Turing machine -> tag system -> cyclic tag system *)

Do[
    With[{tm = ToExpression["tm" <> nm], cfg = ToExpression["cfg" <> nm], nm = nm},
        With[{tag = TuringMachineToTagSystem[tm, cfg], m = Association[tm]},
            VerificationTest[tag["Productions"], ToExpression["productions" <> nm],
                TestID -> "TagProductions" <> nm];
            VerificationTest[tag["Word"], ToExpression["word" <> nm], TestID -> "TagWord" <> nm];
            VerificationTest[TagSystemEvolution[tag, 39], DeleteMissing[ToExpression["tagRun" <> nm]],
                TestID -> "TagRun" <> nm];
            VerificationTest[private["tagTimes"][m, cfg, 4], ToExpression["tagTimes" <> nm],
                TestID -> "TagTimes" <> nm];
            VerificationTest[NestList[private["rawStep"][m], cfg, 4], ToExpression["rawRun" <> nm],
                TestID -> "RawRun" <> nm];
            With[{cts = TagSystemToCyclicTagSystem[tag]},
                VerificationTest[cts, ToExpression["cts" <> nm], TestID -> "CyclicTag" <> nm];
                With[{ev = CyclicTagSystemEvolution[cts, 2028]},
                    VerificationTest[
                        Map[{#["Data"], #["Phase"]} &, ev[[{0, 1, 2, 3, 50, 169, 338, 1000, 2028} + 1]]],
                        ToExpression["ctsRun" <> nm], TestID -> "CyclicTagRun" <> nm]]
            ];
            VerificationTest[
                TagSystemToTuringMachine[
                    CyclicTagSystemToTagSystem[TagSystemToCyclicTagSystem[TuringMachineToTagSystem[tm, #]]["Data"],
                        Length[tag["Productions"]]],
                    tag["States"]] & /@ NestList[private["rawStep"][m], cfg, 2],
                ToExpression["decodeCTS" <> nm], TestID -> "DecodeCyclicTag" <> nm]
        ]],
    {nm, {"H", "Ex"}}
]

(* ::Section:: *)
(* Cyclic tag system -> System 5 *)

VerificationTest[CyclicTagSystemToSystem5[ctsD1, 1], s5D1n1, TestID -> "System5D1"]
VerificationTest[CyclicTagSystemToSystem5[ctsD1, 2], s5D1n2, TestID -> "System5D1Two"]
VerificationTest[CyclicTagSystemToSystem5[ctsD1p1, 1], s5D1p1, TestID -> "System5Phase"]
VerificationTest[CyclicTagSystemToSystem5[ctsD2, 3], s5D2n3, TestID -> "System5D2"]
VerificationTest[System5Evolution[s5D1n1, 11], DeleteMissing[s5Run], TestID -> "System5Run"]
VerificationTest[System5Evolution[s5D2n3, Infinity, "Length"], s5D2n3Length, TestID -> "System5Length"]
VerificationTest[Length[System5Evolution[s5D2n3, 10^5]] - 1, s5D2n3Length, TestID -> "System5LengthSteps"]
VerificationTest[
    missingToNone /@ System5ToCyclicTagSystem /@ {{1, 2, 3, 4, 5, 7, 8, 10}, {2, 1}, {1, 3}, {1, 4}, {0, 1},
        {1, 2, 3}, {}, {5, 6, 3, 4}},
    missingToNone /@ decodeBags, TestID -> "DecodeBag"]

(* ::Section:: *)
(* System 5 -> System 4 *)

VerificationTest[System5ToSystem4[s5D4, 16], s4D4, TestID -> "System4D4"]
VerificationTest[System5ToSystem4[s5D4, 3], s4Small, TestID -> "System4Small"]
VerificationTest[System4Evolution[s4Small, 59], DeleteMissing[s4SmallRun], TestID -> "System4Run"]
VerificationTest[Length[System4Evolution[s4D4, 20000]] - 1, s4D4Length, TestID -> "System4Length"]
With[{ev = System4Evolution[s4Small, 59]},
    VerificationTest[missingToNone[System4ToSystem5[#, 8]] & /@ ev,
        missingToNone /@ Take[decodeS4, Length[ev]], TestID -> "DecodeSystem4"]]
VerificationTest[Values[EmulationParameters[s5D4, "ClosedForm"]][[;; 6]], icD4,
    TestID -> "ClosedFormParameters"]

(* ::Section:: *)
(* System 4 -> System 3 -> wolfram23 *)

VerificationTest[System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3],
    s3D9, TestID -> "System3D9"]
VerificationTest[System4ToSystem3[<|"Elements" -> {{0, 2, 4, 6}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3],
    s3D10, TestID -> "System3D10"]
VerificationTest[System4ToSystem3[<|"Elements" -> {{2}, "*", {0, 3}}, "Active" -> 0, "State" -> "A"|>, 4, 5],
    s3Small, TestID -> "System3Small"]
VerificationTest[System3Evolution[s3D9, 119], DeleteMissing[s3D9Run], TestID -> "System3Run"]
VerificationTest[System3ToWolfram23 /@ System3Evolution[s3D9, 119], DeleteMissing[w23D9Run],
    TestID -> "Relabel"]
VerificationTest[System3ToWolfram23[s3D9], w23D9, TestID -> "Wolfram23D9"]
VerificationTest[Wolfram23Evolution[w23D9, 199], w23D9Steps, TestID -> "Wolfram23Run"]
VerificationTest[missingToNone[Wolfram23ToSystem5[#, 3, 4]] & /@ Wolfram23Evolution[w23D9, 199],
    missingToNone /@ decodeW23D9, TestID -> "DecodeWolfram23"]
VerificationTest[missingToNone[Wolfram23ToSystem5[#, 3, 8]] & /@
        Wolfram23Evolution[System3ToWolfram23[s3D10], 199],
    missingToNone /@ decodeW23D10, TestID -> "DecodeWolfram23D10"]

(* ::Section:: *)
(* The stages track each other *)

VerificationTest[TuringMachineToTagSystem[tmEx, cfgEx, 4]["TagTimes"], tagTimesEx, TestID -> "TagTimesPublic"]

(* the tag words at the tag times decode to the machine's configurations *)
With[{tag = TuringMachineToTagSystem[tmEx, cfgEx, 4]},
    VerificationTest[
        TagSystemToTuringMachine[TagSystemEvolution[tag, 85][[# + 1]], 3] & /@ tag["TagTimes"],
        rawRunEx, TestID -> "TagTracksMachine"]]

(* one cycle of the cyclic tag system is one tag step *)
With[{tag = TuringMachineToTagSystem[tmEx, cfgEx]},
    VerificationTest[
        CyclicTagSystemToTagSystem[#["Data"], 253] & /@
            Values[CyclicTagSystemEvolution[TagSystemToCyclicTagSystem[tag], 506 * 18, #["Phase"] == 0 &]],
        TagSystemEvolution[tag, 18], TestID -> "CyclicTagTracksTag"]]

(* the System 5 bags decode to the run of the doubled cyclic tag system *)
With[{cts = <|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>},
    With[{doubled = <|"Appendants" -> Catenate[{Riffle[#, #], {}} & /@ cts["Appendants"]],
            "Data" -> Riffle[cts["Data"], cts["Data"]], "Phase" -> 0|>,
          decoded = First /@ Split[DeleteMissing[
            System5ToCyclicTagSystem /@ System5Evolution[CyclicTagSystemToSystem5[cts, 3], 1000][[All, "Bag"]]]]},
        VerificationTest[decoded,
            Take[First /@ Split[CyclicTagSystemEvolution[doubled, 12][[All, "Data"]]], Length[decoded]],
            TestID -> "System5TracksCyclicTag"]]]

(* with the proof's parameters the System 4 decodes are the System 5 bags,
   then the terminal phase *)
With[{s5 = <|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>},
    With[{p = EmulationParameters[s5]},
        VerificationTest[
            Take[DeleteDuplicates[Sort /@ DeleteMissing[System4ToSystem5[#, p["Band"]] & /@ Values[
                System4Evolution[System5ToSystem4[s5, p["f"]], 10^6, #["Active"] == 0 && #["State"] === "B" &]]]], 12],
            Sort /@ System5Evolution[s5, 100][[All, "Bag"]], TestID -> "System4TracksSystem5"]]]

(* wolfram23, back at the left end in state B, decodes as System 4 does
   when its head is back on the first set in state B *)
With[{s4 = System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1]},
    With[{d4 = System4ToSystem5[#, 20] & /@ Values[System4Evolution[s4, 1000, #["Active"] == 0 && #["State"] === "B" &]]},
        VerificationTest[
            Take[Wolfram23ToSystem5[#, 7, 20] & /@ Values[
                Wolfram23Evolution[System3ToWolfram23[System4ToSystem3[s4, 7, 120]], 50000, #1 == 2 && #2 == 123 &]],
                Length[d4]],
            d4, TestID -> "Wolfram23TracksSystem4"]]]

(* ::Section:: *)
(* Plots *)

VerificationTest[Head[TagSystemEvolutionPlot[TuringMachineToTagSystem[tmEx, cfgEx], 85]], Graphics, TestID -> "TagPlot"]
VerificationTest[Head[CyclicTagSystemEvolutionPlot[ctsD1, 40]], Graphics, TestID -> "CyclicTagPlot"]
VerificationTest[Head[System5EvolutionPlot[s5D1n1, 20]], Legended, TestID -> "System5Plot"]
VerificationTest[Head[System4EvolutionPlot[s4Small, 60]], Graphics, TestID -> "System4Plot"]
VerificationTest[Head[System3EvolutionPlot[s3D9, 100]], Graphics, TestID -> "System3Plot"]
VerificationTest[Head[Wolfram23EvolutionPlot[w23D9, 10^5, "MaxRows" -> 50]], Graphics, TestID -> "Wolfram23Plot"]
VerificationTest[Head /@ {TuringMachineEvolutionPlot[tmEx, cfgEx, 4], TuringMachineEvolutionPlot[tmEx, cfgEx, 60]}, {Grid, Graphics},
    TestID -> "TuringMachinePlot"]
VerificationTest[Head[TagSystemEvolutionPlot[TuringMachineToTagSystem[tmEx, cfgEx], 18]], Grid, TestID -> "TagPlotLabeled"]

(* ::Section:: *)
(* Parity blocks *)

(* the successive scans of a block read its set back, for every set below 2^w - 2 *)
VerificationTest[
    AllTrue[Subsets[Range[0, 2^4 - 3]], Function[s,
        Flatten[Position[Mod[Total /@ NestList[Mod[Accumulate[#], 2] &, ParityBlock[s, 4] - 1, 2^4 - 3], 2], 1]] - 1 == s]],
    True, TestID -> "ParityBlockScans"]
VerificationTest[First /@ (ParityBlock[#, 3] & /@ {{}, {0}, {1}, {0, 2}}), {2, 2, 2, 2}, TestID -> "ParityBlockStartsWith2"]
