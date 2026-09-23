(* ::Package:: *)

(* Emulation.wl

   The chain of Smith's proof that Wolfram's 2,3 Turing machine is universal,
   as formalized in Lean under Proofs/ (branch lean-proofs):

       Turing machine -> 2-tag system -> cyclic tag system -> System 5
         -> System 4 -> System 3 -> wolfram23 (System 0)

   One function per arrow (the encoders), one per reverse arrow (the
   decoders), an evolution function per system, and the parameters of the
   emulation. Every function transcribes the Lean definition named in its
   usage message; the regression tests compare the two on shared vectors.

   Data, following the Lean structures:
     machine        {{q, a} -> {q', w, d}, ...}, d = 1 (right) or -1 (left);
                    state 0 halts, missing entries go to {0, 0, 1}
     configuration  {q, left, head, right}, left and right nearest cell first
     tag system     <|"Productions" -> {p0, p1, ...}, "Word" -> w|>, symbols
                    0 .. k - 1
     cyclic tag     <|"Appendants" -> {...}, "Data" -> {...}, "Phase" -> p|>,
                    bits 0 and 1
     System 5       <|"Bag" -> {...}, "Rules" -> {{...}, ...}|>
     System 4       <|"Elements" -> {...}, "Active" -> i, "State" -> "A"|>, a
                    set is a list of integers, a star is "*", i counts from 0
     System 3       <|"Left" -> {...}, "Head" -> c, "Right" -> {...},
                    "State" -> "A"|>, cells 0, 1, 2
     wolfram23      {q, left, head, right}, q = 1 (A) or 2 (B) *)

BeginPackage["WolframInstitute`TuringMachine`"]

TuringMachineToTagSystem::usage = "TuringMachineToTagSystem[machine, config] gives the Cocke-Minsky 2-tag system of machine and the tag word of config (Lean TagSystem.tagK, TagSystem.word).\nTuringMachineToTagSystem[machine, config, n] also gives the tag times of the first n steps, at which the tag word is the word of the configuration (Lean TagSystem.tagTime).\nTuringMachineToTagSystem[machine] gives the tag system alone."

TagSystemToCyclicTagSystem::usage = "TagSystemToCyclicTagSystem[tag] gives Cook's cyclic tag system of the 2-tag system tag and the encoding of its word (Lean TagSystem.tagToCTS, TagSystem.tagConfigToCTS)."

CyclicTagSystemToSystem5::usage = "CyclicTagSystemToSystem5[cts, n] gives Smith's System 5 program for n cycles of the cyclic tag system cts (Lean BiTM.ctsToSystem5)."

System5ToSystem4::usage = "System5ToSystem4[s5, f] gives the System 4 tape of the System 5 program s5 with the parameter f (Lean BiTM.system5ToSystem4)."

System4ToSystem3::usage = "System4ToSystem3[s4, w, h] gives the System 3 tape of the System 4 tape s4 with blocks of width 2^w and a left end of h zeros (Lean Smith.initAC, Smith.AC.toL)."

System3ToWolfram23::usage = "System3ToWolfram23[s3] gives the wolfram23 configuration of the System 3 configuration s3 (Lean Smith.phi3, Smith.phi2, Smith.toBi)."

TagSystemToTuringMachine::usage = "TagSystemToTuringMachine[word, s] decodes a Cocke-Minsky tag word of a machine with states below s to the machine configuration, without trailing blanks (Lean TagSystem.decodeWord)."

CyclicTagSystemToTagSystem::usage = "CyclicTagSystemToTagSystem[data, k] decodes cyclic tag data to the tag word over k symbols, or gives Missing when data is not an encoding (Lean TagSystem.tagWordDecode)."

System5ToCyclicTagSystem::usage = "System5ToCyclicTagSystem[bag] decodes a System 5 bag to the doubled cyclic tag data, or gives Missing (Lean decodeBag)."

System4ToSystem5::usage = "System4ToSystem5[s4, b] decodes the leading sets of the System 4 tape s4 below the band b to a System 5 bag, or gives Missing (Lean Smith.decodeS4)."

Wolfram23ToSystem5::usage = "Wolfram23ToSystem5[config, w, b] decodes the leading blocks of width 2^w right of the head of a wolfram23 configuration below the band b to a System 5 bag, or gives Missing (Lean Smith.decodeBlocks)."

TagSystemEvolution::usage = "TagSystemEvolution[tag, n] gives the words of the 2-tag system tag for n steps or until it halts.\nTagSystemEvolution[tag, n, crit] gives the rules t -> w for the steps t whose word satisfies crit."

CyclicTagSystemEvolution::usage = "CyclicTagSystemEvolution[cts, n] gives the configurations of the cyclic tag system cts for n steps or until its data is empty.\nCyclicTagSystemEvolution[tag, n, crit] gives the rules t -> c for the steps t whose configuration satisfies crit."

System5Evolution::usage = "System5Evolution[s5, n] gives the configurations of the System 5 program s5 for n steps or until it halts.\nSystem5Evolution[s5, n, \"Length\"] gives the length of the run within n steps.\nSystem5Evolution[s5, n, crit] gives the rules t -> c for the steps t whose configuration satisfies crit."

System4Evolution::usage = "System4Evolution[s4, n] gives the configurations of the System 4 tape s4 for n steps or until it halts.\nSystem4Evolution[s4, n, crit] gives the rules t -> config for the steps t whose configuration satisfies crit."

System3Evolution::usage = "System3Evolution[s3, n] gives the configurations of the System 3 tape s3 for n steps or until it halts.\nSystem3Evolution[s3, n, crit] gives the rules t -> c for the steps t whose configuration satisfies crit."

Wolfram23Evolution::usage = "Wolfram23Evolution[config, n] gives the configurations of Wolfram's 2,3 machine from config for n steps.\nWolfram23Evolution[config, n, crit] gives the rules t -> config for the steps t at which crit[state, position] is True, position being the number of cells left of the head."

EmulationParameters::usage = "EmulationParameters[s5] gives the parameters of the emulation of the System 5 program s5 by wolfram23, from the exact run lengths.\nEmulationParameters[s5, \"ClosedForm\"] gives them from the closed-form run bounds of the Lean initial condition Smith.icStart."

EmulationSizes::usage = "EmulationSizes[machine, config, n] gives the size of every stage of the emulation of n steps of machine from config, without building the large stages."

TagSystemEvolutionPlot::usage = "TagSystemEvolutionPlot[tag, n] plots the words of the 2-tag system tag for n steps, each word at its position in the queue."

CyclicTagSystemEvolutionPlot::usage = "CyclicTagSystemEvolutionPlot[cts, n] plots the working strings of the cyclic tag system cts for n steps, each at its position in the queue, the rows where a cycle starts marked."

System5EvolutionPlot::usage = "System5EvolutionPlot[s5, n] plots the bag of the System 5 program s5 at every step of its run, the steps where a rule is popped marked."

System4EvolutionPlot::usage = "System4EvolutionPlot[s4, n] plots the tape of the System 4 configuration s4 at every step: sets, stars and the active element colored by the state."

System3EvolutionPlot::usage = "System3EvolutionPlot[s3, n] plots the tape of the System 3 configuration s3 at every step, the active cell colored by the state."

Wolfram23EvolutionPlot::usage = "Wolfram23EvolutionPlot[config, n] plots the tape of Wolfram's 2,3 machine from config for n steps, the head colored by the state."

Begin["`Private`"]

(* ::Section:: *)
(* Machines *)

machineAssoc[rules_List] := Association[rules]

transition[m_Association, q_Integer, a_Integer] := Lookup[m, Key[{q, a}], {0, 0, 1}]

numStates[m_Association] := 1 + Max[0, Keys[m][[All, 1]], Values[m][[All, 1]]]

(* val: a tape half as a number, nearest cell least significant *)
tapeValue[l_List] := Total[l 2^Range[0, Length[l] - 1]]

natBits[0] = {};
natBits[n_Integer] := IntegerDigits[n, 2] // Reverse

(* the step with the halting state read as an ordinary one (TagSystem.rawStep) *)
rawStep[m_Association][{q_, l_, h_, r_}] := With[{rule = transition[m, q, h]},
    If[rule[[3]] == 1,
        {rule[[1]], Prepend[l, rule[[2]]], If[r === {}, 0, First[r]], If[r === {}, {}, Rest[r]]},
        {rule[[1]], If[l === {}, {}, Rest[l]], If[l === {}, 0, First[l]], Prepend[r, rule[[2]]]}]]

(* the tag steps of one raw step (TagSystem.roundLen) *)
roundLen[m_Association][{q_, l_, h_, r_}] := Module[
    {a = tapeValue[l], n = h + 2 tapeValue[r], base},
    base = (a + n + 2) + 2 (a + Quotient[n, 2] + 2);
    If[transition[m, q, h][[3]] == 1, base,
        base + 2 (Quotient[a, 2] + 2 Quotient[n, 2] + 2)]
]

tagTimes[m_Association, cfg_, n_] :=
    Prepend[Accumulate[roundLen[m] /@ Most[NestList[rawStep[m], cfg, n]]], 0]

(* the rules t -> c of a run for the configurations c that satisfy crit,
   keeping only those *)
evolveSelect[step_, c0_, n_, crit_] := Module[{c = c0, next, t = 0, out = {}},
    If[TrueQ[crit[c]], AppendTo[out, 0 -> c]];
    While[t < n && !MissingQ[next = step[c]],
        c = next; t++;
        If[TrueQ[crit[c]], AppendTo[out, t -> c]]];
    out
]

(* ::Section:: *)
(* Turing machine -> 2-tag system (TagSystem/CockeMinsky.lean, TMToCTS.lean) *)

$kinds = {"A", "al", "B", "be", "P1", "P0", "p", "Q", "r", "E", "e", "F", "f",
    "G", "g", "H", "k", "I", "i", "J", "j"};
kindIndex = AssociationThread[$kinds -> Range[0, 20]];

(* a symbol is X (the pad) or sym[kind, q, h, b] *)
sy[kd_, q_, h_ : 0, b_ : 0] := sym[kd, q, h, b]

pad[h_] := If[h == 1, {}, {X}]
pairs2[a_, b_, m_] := Flatten[ConstantArray[{a, b}, m], 1] /; m > 0
pairs2[_, _, _] := {}

cmProduction[_, X] := {}
cmProduction[m_, sym[kd_, q_, h_, b_]] := Module[
    {rule = transition[m, q, h], nq, wr, dir},
    {nq, wr, dir} = {rule[[1]], Mod[rule[[2]], 2], rule[[3]]};
    Switch[kd,
        "A", {sy["P1", q], sy["P0", q]},
        "al", {sy["p", q], sy["p", q]},
        "B", {sy["Q", q]},
        "be", {sy["r", q]},
        "P1", {sy["E", q, 1], sy["E", q, 0]},
        "P0", {},
        "p", {sy["e", q, 1], sy["e", q, 0]},
        "Q", {sy["F", q, 1], sy["F", q, 0]},
        "r", {sy["f", q, 1], sy["f", q, 0]},
        "E", If[dir == 1,
            Join[pad[h], {sy["A", nq], X}, pairs2[sy["al", nq], X, wr]],
            Join[pad[h], {sy["G", q, h]}]],
        "e", If[dir == 1, {sy["al", nq], X, sy["al", nq], X}, {sy["g", q, h]}],
        "F", If[dir == 1, {sy["B", nq], X}, {sy["H", q, h], sy["H", q, h]}],
        "f", If[dir == 1, {sy["be", nq], X}, ConstantArray[sy["k", q, h], 4]],
        "G", {sy["I", q, h, 1], sy["I", q, h, 0]},
        "g", {sy["i", q, h, 1], sy["i", q, h, 0]},
        "H", {sy["J", q, h, 1], sy["J", q, h, 0]},
        "k", {sy["j", q, h, 1], sy["j", q, h, 0]},
        "I", Join[pad[b], {sy["A", nq], X}],
        "i", {sy["al", nq], X},
        "J", Join[{sy["B", nq], X}, pairs2[sy["be", nq], X, 2 wr + b]],
        "j", {sy["be", nq], X, sy["be", nq], X}
    ]
]

encSym[s_, X] := 0
encSym[s_, sym[kd_, q_, h_, b_]] := Mod[1 + (kindIndex[kd] s + q) 4 + 2 h + b, 1 + 84 s]

decSym[s_, 0] := X
decSym[s_, i_Integer] := With[{n = i - 1},
    sym[$kinds[[Min[Quotient[Quotient[n, 4], s], 20] + 1]], Mod[Quotient[n, 4], s],
        Quotient[Mod[n, 4], 2], Mod[n, 2]]]

cword[q_, m_, n_] := Join[{sy["A", q], X}, pairs2[sy["al", q], X, m], {sy["B", q], X},
    pairs2[sy["be", q], X, n]]

tagWord[{q_, l_, h_, r_}] := cword[q, tapeValue[l], h + 2 tapeValue[r]]

TuringMachineToTagSystem[rules_List] := Module[{m = machineAssoc[rules], s},
    s = numStates[m];
    <|"Productions" -> Table[encSym[s, #] & /@ cmProduction[m, decSym[s, i]], {i, 0, 84 s}],
      "States" -> s|>
]

TuringMachineToTagSystem[rules_List, cfg : {_Integer, _List, _Integer, _List}] := With[
    {tag = TuringMachineToTagSystem[rules]},
    Append[tag, "Word" -> (encSym[tag["States"], #] & /@ tagWord[cfg])]
]

TuringMachineToTagSystem[rules_List, cfg : {_Integer, _List, _Integer, _List}, n_Integer?NonNegative] :=
    Append[TuringMachineToTagSystem[rules, cfg], "TagTimes" -> tagTimes[machineAssoc[rules], cfg, n]]

(* decoder: TagSystem.parseWord, cfgOfNums *)
countPairs[a_, l_List] := Module[{n = 0, r = l},
    While[Length[r] >= 2 && r[[1]] === a && r[[2]] === X, n++; r = Drop[r, 2]];
    {n, r}
]

parseWord[{sym["A", q_, _, _], X, rest___}] := Module[{r1, r3},
    r1 = countPairs[sym["al", q, 0, 0], {rest}];
    Replace[r1[[2]], {
        {sym["B", q, _, _], X, rest2___} :> (
            r3 = countPairs[sym["be", q, 0, 0], {rest2}];
            If[r3[[2]] === {}, {q, r1[[1]], r3[[1]]}, Missing["NotAWord"]]),
        _ -> Missing["NotAWord"]}]
]
parseWord[_] := Missing["NotAWord"]

TagSystemToTuringMachine[word_List, s_Integer] := Replace[parseWord[decSym[s, #] & /@ word], {
    {q_, m_, n_} :> {q, natBits[m], Mod[n, 2], natBits[Quotient[n, 2]]}}]

(* ::Section:: *)
(* 2-tag system -> cyclic tag system (TagSystem/TagToCTS.lean) *)

symbolEncode[k_, i_] := Table[Boole[j == i], {j, 0, k - 1}]
tagWordEncode[k_, w_List] := Flatten[symbolEncode[k, #] & /@ w]

TagSystemToCyclicTagSystem[tag_Association] := Module[{prods = tag["Productions"], k},
    k = Length[prods];
    <|"Appendants" -> Join[tagWordEncode[k, #] & /@ prods, ConstantArray[{}, k]],
      "Data" -> tagWordEncode[k, Lookup[tag, "Word", {}]],
      "Phase" -> 0|>
]

CyclicTagSystemToTagSystem[data_List, k_Integer] := Module[{blocks},
    If[Mod[Length[data], k] != 0, Return[Missing["NotAnEncoding"]]];
    blocks = Partition[data, k];
    If[AllTrue[blocks, Count[#, 1] == 1 && Count[#, 0] == k - 1 &],
        (FirstPosition[#, 1][[1]] - 1) & /@ blocks,
        Missing["NotAnEncoding"]]
]

(* ::Section:: *)
(* Cyclic tag system -> System 5 (BiTM/CTSToSystem5.lean) *)

bagAux[data_List] := Module[{i = 1, out = {}},
    Do[If[b == 1,
            out = Join[out, {i, i + 2, i + 3, i + 5}]; i += 6,
            out = Join[out, {i, i + 1, i + 2, i + 3}]; i += 4],
        {b, data}];
    out
]

encodeAppendant[a_List, i0_] := Module[{i = i0, r1 = {}, r2 = {}},
    Do[If[b == 1,
            AppendTo[r1, i + 2]; AppendTo[r1, i + 5]; AppendTo[r2, i]; AppendTo[r2, i + 3]; i += 6,
            AppendTo[r1, i + 2]; AppendTo[r1, i + 3]; AppendTo[r2, i]; AppendTo[r2, i + 1]; i += 4],
        {b, a}];
    {r1, r2, i}
]

processCycle[apps_List, i0_] := Module[{i = i0, out = {}, r1, r2},
    Do[{r1, r2, i} = encodeAppendant[a, i]; out = Join[out, {r1, r2, {}, {}}], {a, apps}];
    {out, i}
]

CyclicTagSystemToSystem5[cts_Association, n_Integer?NonNegative] := Module[
    {apps = cts["Appendants"], data = cts["Data"], i, cyc, rules = {}},
    apps = RotateLeft[apps, Mod[Lookup[cts, "Phase", 0], Length[apps]]];
    i = 1 + Total[If[# == 1, 6, 4] & /@ data] + 2;
    Do[{cyc, i} = processCycle[apps, i]; rules = Join[rules, cyc], {n}];
    <|"Bag" -> bagAux[data], "Rules" -> rules|>
]

(* decodeBag: sort, then read pairs with gaps 1 (0) and 2 (1) above 0 *)
System5ToCyclicTagSystem[bag_List] := Module[{l = Sort[bag], lo = 0, out = {}},
    If[OddQ[Length[l]], Return[Missing["NotAnEncoding"]]];
    Do[With[{x = l[[j]], y = l[[j + 1]]},
        If[lo < x && (y == x + 1 || y == x + 2),
            AppendTo[out, y - x - 1]; lo = y,
            Return[Missing["NotAnEncoding"], Module]]],
        {j, 1, Length[l], 2}];
    out
]

(* ::Section:: *)
(* System 5 (BiTM/System5.lean, BiTM/XorMerge.lean) *)

xorInsert[x_, xs_List] := If[MemberQ[xs, x], deleteFirst[xs, x], Prepend[xs, x]]
deleteFirst[xs_List, x_] := With[{p = FirstPosition[xs, x, None, {1}]},
    If[p === None, xs, Delete[xs, p]]]
xorMerge[xs_List, ys_List] := Fold[xorInsert[#2, #1] &, xs, ys]

system5Step[s_Association] := Module[{d = s["Bag"] - 1, r = s["Rules"]},
    Which[
        d === {} || r === {}, Missing["Halted"],
        MemberQ[d, 0],
            <|"Bag" -> xorMerge[deleteFirst[d, 0], r[[1]] + 1], "Rules" -> Rest[r] + 1|>,
        True, <|"Bag" -> d, "Rules" -> r + 1|>
    ]
]

System5Evolution[s_Association, n_Integer?NonNegative] :=
    NestWhileList[system5Step, s, !MissingQ[#] &, 1, n] // DeleteMissing

System5Evolution[s_Association, n_Integer?NonNegative, crit : Except["Length"]] :=
    evolveSelect[system5Step, s, n, crit]

(* the run length without building the configurations: bag entries as
   deadlines, rule entries shifted by the time *)
System5Evolution[s_Association, n : (_Integer?NonNegative | Infinity), "Length"] /;
    inv5Q[s] := Module[
    {present = Association[Thread[s["Bag"] -> True]], queue = CreateDataStructure["PriorityQueue"],
     t = 0, k = 1, rules = s["Rules"], m, toggle},
    (* a max-queue of negated deadlines, stale entries skipped on pop *)
    Scan[queue["Push", -#] &, s["Bag"]];
    toggle[d_] := If[KeyExistsQ[present, d], KeyDropFrom[present, d], present[d] = True; queue["Push", -d]];
    While[Length[present] > 0 && k <= Length[rules],
        While[!KeyExistsQ[present, m = -queue["Pop"]]];
        If[m > n, Return[n, Module]];
        t = m;
        KeyDropFrom[present, m];
        Scan[toggle[# + 2 t] &, rules[[k]]];
        k++
    ];
    Min[t, n]
]

(* outside the invariant of the encoder's output, step by step *)
System5Evolution[s_Association, n : (_Integer?NonNegative | Infinity), "Length"] := Module[
    {c = s, t = 0},
    While[t < n && !MissingQ[c = system5Step[c]], t++];
    t
]

(* Smith.Inv5: a duplicate-free bag of positive entries, rule entries >= 0 *)
inv5Q[s_Association] := DuplicateFreeQ[s["Bag"]] && AllTrue[s["Bag"], # >= 1 &] &&
    AllTrue[Flatten[s["Rules"]], # >= 0 &]

(* ::Section:: *)
(* System 5 -> System 4 (BiTM/System5ToSystem4.lean) *)

starredEmptyPairs[n_] := Flatten[ConstantArray[{"*", {}}, n], 1]

encodeBag[bag_List] := Fold[xorInsert[2 #2 - 2, #1] &, {}, bag]

encodeRuleSet[rule_List, f_] := Fold[xorInsert[2 #2 + f + 3, #1] &, Range[0, 3 f], rule]

encodeRuleElements[rule_List, f_] := Join[
    {"*", encodeRuleSet[rule, f]}, starredEmptyPairs[2 f],
    {"*", Range[0, 3 f]}, starredEmptyPairs[Max[2 f - 2, 0]]]

System5ToSystem4[s_Association, f_Integer?Positive] := <|
    "Elements" -> Join[{encodeBag[s["Bag"]]}, starredEmptyPairs[f],
        Flatten[encodeRuleElements[#, f] & /@ s["Rules"], 1]],
    "Active" -> 0, "State" -> "A"|>

(* ::Section:: *)
(* System 4 (BiTM/System4.lean) *)

system4Step[c_Association] := Module[
    {el = c["Elements"], a = c["Active"], st = c["State"], e},
    If[a >= Length[el], Return[Missing["Halted"]]];
    e = el[[a + 1]];
    Which[
        e === "*" && st === "A", <|c, "Elements" -> Delete[el, a + 1], "State" -> "B"|>,
        ListQ[e] && st === "A",
            If[a == 0, <|c, "State" -> "B"|>, <|c, "Active" -> a - 1|>],
        ListQ[e],
            With[{zero = MemberQ[e, 0]},
                <|"Elements" -> ReplacePart[el, a + 1 -> If[zero, deleteFirst[e, 0], e] - 1],
                  "Active" -> a + 1,
                  "State" -> If[zero, st /. {"B" -> "C", "C" -> "B"}, st]|>],
        st === "B",
            If[a == 0, Missing["Halted"],
                <|"Elements" -> Delete[el, a + 1], "Active" -> a - 1, "State" -> "A"|>],
        True, (* star in state C *)
            If[a + 1 < Length[el] && ListQ[el[[a + 2]]],
                <|"Elements" -> ReplacePart[el, a + 2 -> xorInsert[1, el[[a + 2]]]],
                  "Active" -> a + 1, "State" -> "C"|>,
                Missing["Halted"]]
    ]
]

System4Evolution[c_Association, n_Integer?NonNegative] :=
    NestWhileList[system4Step, c, !MissingQ[#] &, 1, n] // DeleteMissing

System4Evolution[c_Association, n_Integer?NonNegative, crit_] := evolveSelect[system4Step, c, n, crit]

(* decodeS4: the parity set of the leading sets below the band *)
System4ToSystem5[c_Association, b_Integer?NonNegative] := Module[{lead, xs},
    lead = TakeWhile[c["Elements"], ListQ];
    xs = Select[Range[0, b - 1], OddQ[Count[lead, set_ /; MemberQ[set, #]]] &];
    If[AllTrue[xs, EvenQ], xs/2 + 1, Missing["NotAnEncoding"]]
]

(* ::Section:: *)
(* System 4 -> System 3 (Smith/ParityBlocks.lean, Smith/Conjecture3.lean) *)

(* row n i: Smith's string for {i}, rule 60 from 2 1 1 ... 1; cell j is
   Binomial[i, j] mod 2 *)
row[n_, i_] := Table[Boole[BitAnd[i, j] == j], {j, 0, n - 1}]

baseSet[n_, set_List] := Fold[BitXor[row[n, #2], #1] &, ConstantArray[1, n], Reverse[set]]

encSet[n_, set_List] := With[{x = baseSet[n, set]},
    If[First[x] == 1, x, BitXor[x, row[n, Max[n - 2, 0]]]]]

toCell[bits_List] := bits + 1

renderRight[items_List] := Module[{afterStar = False},
    Flatten[Function[it, If[it === "*",
        afterStar = True; {0},
        With[{x = toCell[it]}, If[afterStar, afterStar = False; Rest[x], x]]]] /@ items]
]

System4ToSystem3[c_Association, w_Integer?NonNegative, h_Integer?NonNegative] := Module[
    {el = c["Elements"], n = 2^w, x0},
    x0 = encSet[n, First[el]];
    <|"Left" -> Join[{1, 2, 2}, ConstantArray[0, h]],
      "Head" -> First[x0] + 1,
      "Right" -> Join[toCell[Rest[x0]],
          renderRight[If[# === "*", "*", encSet[n, #]] & /@ Rest[el]], {1}],
      "State" -> "A"|>
] /; c["Active"] == 0 && c["State"] === "A" && ListQ[First[c["Elements"]]]

(* ::Section:: *)
(* System 3 (Smith/Lookahead.lean) *)

(* a rule is {"one", state, cell, dir} or {"two", state, cell, right, dir} *)
sys3Rule["A", 0, _] := {"one", "B", 2, 1}
sys3Rule["A", 1, _] := {"one", "A", 1, -1}
sys3Rule["A", 2, _] := {"one", "A", 2, -1}
sys3Rule["B", 0, _] := {"one", "A", 2, -1}
sys3Rule["B", 1, _] := {"one", "B", 1, 1}
sys3Rule["B", 2, 0] := {"two", "A", 0, 0, 1}
sys3Rule["B", 2, 1] := {"two", "C", 2, 1, 1}
sys3Rule["B", 2, 2] := {"two", "C", 2, 2, 1}
sys3Rule["C", 0, _] := {"one", "A", 2, -1}
sys3Rule["C", 1, 0] := {"two", "A", 0, 0, 1}
sys3Rule["C", 1, 1] := {"two", "C", 2, 1, 1}
sys3Rule["C", 1, 2] := {"two", "C", 2, 2, 1}
sys3Rule["C", 2, _] := {"one", "B", 1, 1}

system3Step[c_Association] := Module[
    {l = c["Left"], h = c["Head"], r = c["Right"], st = c["State"], rule},
    If[r === {},
        rule = sys3Rule[st, h, 0];
        Return[If[rule[[1]] === "one" && rule[[4]] == -1 && l =!= {},
            <|"Left" -> Rest[l], "Head" -> First[l], "Right" -> {rule[[3]]}, "State" -> rule[[2]]|>,
            Missing["Halted"]]]];
    rule = sys3Rule[st, h, First[r]];
    Switch[rule,
        {"one", _, _, 1}, <|"Left" -> Prepend[l, rule[[3]]], "Head" -> First[r],
            "Right" -> Rest[r], "State" -> rule[[2]]|>,
        {"one", _, _, -1}, If[l === {}, Missing["Halted"],
            <|"Left" -> Rest[l], "Head" -> First[l], "Right" -> Prepend[r, rule[[3]]],
              "State" -> rule[[2]]|>],
        {"two", _, _, _, 1}, <|"Left" -> Prepend[l, rule[[3]]], "Head" -> rule[[4]],
            "Right" -> Rest[r], "State" -> rule[[2]]|>,
        _, If[l === {}, Missing["Halted"],
            <|"Left" -> Rest[l], "Head" -> First[l],
              "Right" -> Join[{rule[[3]], rule[[4]]}, Rest[r]], "State" -> rule[[2]]|>]
    ]
]

System3Evolution[c_Association, n_Integer?NonNegative] :=
    NestWhileList[system3Step, c, !MissingQ[#] &, 1, n] // DeleteMissing

System3Evolution[c_Association, n_Integer?NonNegative, crit_] := evolveSelect[system3Step, c, n, crit]

(* ::Section:: *)
(* System 3 -> wolfram23 (Smith/Systems123.lean, Smith/Wolfram23Bridge.lean) *)

sw[c_] := {0, 2, 1}[[c + 1]]

System3ToWolfram23[c_Association] := Module[{st = c["State"], h = c["Head"]},
    {Replace[st, {"A" -> 1, "B" -> 2, "C" -> 2}], sw /@ c["Left"],
     If[st === "A" || st === "C", sw[h], h], c["Right"]}
]

$wolfram23 = <|{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 2, -1}, {1, 2} -> {1, 1, -1},
    {2, 0} -> {1, 2, -1}, {2, 1} -> {2, 2, 1}, {2, 2} -> {1, 0, 1}|>;

wolfram23Step[{q_, l_, h_, r_}] := With[{rule = $wolfram23[{q, h}]},
    If[rule[[3]] == 1,
        {rule[[1]], Prepend[l, rule[[2]]], If[r === {}, 0, First[r]], If[r === {}, {}, Rest[r]]},
        {rule[[1]], If[l === {}, {}, Rest[l]], If[l === {}, 0, First[l]], Prepend[r, rule[[2]]]}]
]

Wolfram23Evolution[cfg : {_Integer, _List, _Integer, _List}, n_Integer?NonNegative] :=
    NestList[wolfram23Step, cfg, n]

(* the run on a mutable tape, building a configuration only where crit holds *)
$wolfram23Table = {{{2, 1, 1}, {1, 2, -1}, {1, 1, -1}}, {{1, 2, -1}, {2, 2, 1}, {1, 0, 1}}};

Wolfram23Evolution[{q0_Integer, l0_List, h0_Integer, r0_List}, n_Integer?NonNegative, crit_] := Module[
    {tape = Join[Reverse[l0], {h0}, r0], pos = Length[l0] + 1, q = q0, t = 0, out = {}, rule, config},
    config[] := {q, Reverse[tape[[;; pos - 1]]], tape[[pos]], tape[[pos + 1 ;;]]};
    If[TrueQ[crit[q, pos - 1]], AppendTo[out, 0 -> config[]]];
    While[t < n,
        rule = $wolfram23Table[[q, tape[[pos]] + 1]];
        tape[[pos]] = rule[[2]]; q = rule[[1]]; pos += rule[[3]];
        If[pos == 0, PrependTo[tape, 0]; pos = 1];
        If[pos > Length[tape], AppendTo[tape, 0]];
        t++;
        If[TrueQ[crit[q, pos - 1]], AppendTo[out, t -> config[]]]];
    out
]

(* decodeBlocks: the XOR of the leading blocks, read by parity scans *)
parityScans[x_List, b_] := Module[{y = x, out = {}},
    Do[AppendTo[out, Mod[Total[y], 2]]; y = Mod[Accumulate[y], 2], {b}];
    out
]

Wolfram23ToSystem5[{_, _, h_, r_}, w_Integer?NonNegative, b_Integer?NonNegative] := Module[
    {cells = Prepend[TakeWhile[r, # != 0 &], h], n = 2^w, x, xs},
    If[!AllTrue[cells, MemberQ[{1, 2}, #] &] || Length[cells] < n || Mod[Length[cells], n] != 0,
        Return[Missing["NotAnEncoding"]]];
    x = Fold[BitXor, Partition[Boole[# == 2] & /@ cells, n]];
    xs = Flatten[Position[parityScans[x, b], 1] - 1];
    If[AllTrue[xs, EvenQ], xs/2 + 1, Missing["NotAnEncoding"]]
]

(* ::Section:: *)
(* Parameters (Smith/ClosedForm.lean) and sizes *)

maxInt5[s_Association] := Max[0, Flatten[{s["Bag"], s["Rules"]}]]

system4RunLength[c0_Association] := Module[{c = c0, t = 0},
    While[!MissingQ[c = system4Step[c]], t++];
    t
]

(* T5 .. w of Smith.ClosedForm, with the exact run lengths or the bounds *)
emulationParameters[b0_, r_, t5_, t4f_] := Module[{m, h, f, band, l4, t4, fuel},
    m = b0 + t5; h = t5 + m + 1; f = b0 + 2 h + 2 t5 + 5; band = 2 f - 2 t5 - 2;
    l4 = 1 + 2 f + 8 f r;
    t4 = t4f[f, l4];
    fuel = t4 + band;
    <|"B" -> b0, "T5" -> t5, "M" -> m, "H" -> h, "f" -> f, "Band" -> band,
      "System4Length" -> l4, "T4" -> t4, "Fuel" -> fuel, "w" -> BitLength[fuel + 3 f + 6]|>
]

EmulationParameters[s_Association, "Exact"] := emulationParameters[maxInt5[s], Length[s["Rules"]],
    System5Evolution[s, Infinity, "Length"],
    system4RunLength[System5ToSystem4[s, #1]] &]

EmulationParameters[s_Association, "ClosedForm"] := emulationParameters[maxInt5[s], Length[s["Rules"]],
    maxInt5[s] 2^Length[s["Rules"]], (2 #2 + 2) (#2 + 1) &]

EmulationParameters[s_Association] := EmulationParameters[s, "Exact"]

EmulationSizes[rules_List, cfg : {_Integer, _List, _Integer, _List}, n_Integer?NonNegative] := Module[
    {m = machineAssoc[rules], tag, cts, cycles, s5, p},
    tag = TuringMachineToTagSystem[rules, cfg];
    cts = TagSystemToCyclicTagSystem[tag];
    cycles = Last[tagTimes[m, cfg, n]];
    s5 = CyclicTagSystemToSystem5[cts, cycles];
    (* the System 4 run is at least one sweep of its tape; the exact length
       would need the tape itself *)
    p = emulationParameters[maxInt5[s5], Length[s5["Rules"]],
        System5Evolution[s5, Infinity, "Length"], #2 &];
    <|"TagSymbols" -> Length[tag["Productions"]], "TagWord" -> Length[tag["Word"]],
      "TagSteps" -> cycles, "CyclicTagData" -> Length[cts["Data"]],
      "Appendants" -> Length[cts["Appendants"]],
      "System5Rules" -> Length[s5["Rules"]], "System5Integers" -> Length[Flatten[s5["Rules"]]],
      "System5Steps" -> p["T5"], "f" -> p["f"], "System4Elements" -> p["System4Length"],
      "Wolfram23CellsAtLeast" -> Ceiling[p["System4Length"]/2] 2^p["w"]|>
]

(* ::Section:: *)
(* Tag and cyclic tag evolution (TagSystem/Basic.lean) *)

tagStep[prods_][w_List] := If[Length[w] < 2, Missing["Halted"], Join[Drop[w, 2], prods[[w[[1]] + 1]]]]

TagSystemEvolution[tag_Association, n_Integer?NonNegative] :=
    NestWhileList[tagStep[tag["Productions"]], tag["Word"], !MissingQ[#] &, 1, n] // DeleteMissing

TagSystemEvolution[tag_Association, n_Integer?NonNegative, crit_] :=
    evolveSelect[tagStep[tag["Productions"]], tag["Word"], n, crit]

ctsStep[apps_][c_Association] := With[{d = c["Data"], p = c["Phase"]},
    If[d === {}, Missing["Halted"],
        <|"Appendants" -> apps,
          "Data" -> If[First[d] == 1, Join[Rest[d], apps[[Mod[p, Length[apps]] + 1]]], Rest[d]],
          "Phase" -> Mod[p + 1, Length[apps]]|>]]

CyclicTagSystemEvolution[cts_Association, n_Integer?NonNegative] :=
    NestWhileList[ctsStep[cts["Appendants"]], cts, !MissingQ[#] &, 1, n] // DeleteMissing

CyclicTagSystemEvolution[cts_Association, n_Integer?NonNegative, crit_] :=
    evolveSelect[ctsStep[cts["Appendants"]], cts, n, crit]


(* ::Section:: *)
(* Plots *)

Options[evolutionPlot] = {"MaxRows" -> 400, ImageSize -> Automatic, AspectRatio -> 1};

(* the configurations of a run at no more than "MaxRows" evenly spaced steps, without
   keeping the others *)
sampledRun[step_, c0_, n_, maxRows_] := Module[{k = Max[1, Ceiling[n/maxRows]], c = c0, next, t = 0, out = {c0}},
    While[t < n && !MissingQ[next = step[c]],
        c = next; t++;
        If[Mod[t, k] == 0, AppendTo[out, c]]];
    {out, k}
]

rowTicks[k_, rows_] := {{Table[{i, (i - 1) k}, {i, 1, rows, Max[1, Floor[rows/6]]}], None}, {None, None}}

(* a queue: row t starts where the word has been consumed to, so the run slants *)
queuePlot[rows_List, offsets_List, k_, rules_, opts___] := Module[{w = Max[offsets + Length /@ rows]},
    ArrayPlot[MapThread[PadRight[Join[ConstantArray[-1, #2], #1], w, -1] &, {rows, offsets}],
        ColorRules -> Append[rules, -1 -> White], FrameTicks -> rowTicks[k, Length[rows]],
        Frame -> True, opts]
]

TagSystemEvolutionPlot[tag_Association, n_Integer?NonNegative, opts : OptionsPattern[evolutionPlot]] := Module[
    {run, k, s = Lookup[tag, "States", None], color},
    {run, k} = sampledRun[tagStep[tag["Productions"]], tag["Word"], n, OptionValue["MaxRows"]];
    (* symbols colored by their kind when the tag system comes from a machine, else by index *)
    color[0] = GrayLevel[0.85];
    color[i_] := If[IntegerQ[s], ColorData[54][Quotient[i - 1, 4 s] + 1], ColorData[54][i]];
    queuePlot[run, 2 k Range[0, Length[run] - 1], k,
        Table[i -> color[i], {i, 0, Max[Flatten[run], 0]}], ImageSize -> OptionValue[ImageSize],
        AspectRatio -> OptionValue[AspectRatio]]
]

CyclicTagSystemEvolutionPlot[cts_Association, n_Integer?NonNegative, opts : OptionsPattern[evolutionPlot]] := Module[
    {run, k},
    {run, k} = sampledRun[ctsStep[cts["Appendants"]], cts, n, OptionValue["MaxRows"]];
    queuePlot[If[#["Phase"] == 0, 2 #["Data"] + 2, #["Data"]] & /@ run, k Range[0, Length[run] - 1], k,
        {0 -> GrayLevel[0.92], 1 -> GrayLevel[0.2], 2 -> RGBColor[1, 0.85, 0.8], 4 -> RGBColor[0.7, 0.1, 0.1]},
        ImageSize -> OptionValue[ImageSize], AspectRatio -> OptionValue[AspectRatio]]
]

System5EvolutionPlot[s5_Association, n_Integer?NonNegative, opts : OptionsPattern[evolutionPlot]] := Module[
    {run, k, pops},
    {run, k} = sampledRun[system5Step, s5, n, OptionValue["MaxRows"]];
    pops = Flatten[Position[Differences[Length /@ run[[All, "Rules"]]], _?Negative]];
    ListPlot[{Catenate[MapIndexed[Thread[{#1, (First[#2] - 1) k}] &, run[[All, "Bag"]]]],
            Catenate[Thread[{#, pops[[#2]] k}] & @@@ Transpose[{run[[pops + 1, "Bag"]], Range[Length[pops]]}]]},
        PlotStyle -> {Directive[GrayLevel[0.2], PointSize[Small]], Directive[RGBColor[0.8, 0.1, 0.1], PointSize[Medium]]},
        ScalingFunctions -> {None, "Reverse"}, Frame -> True, FrameLabel -> {"bag element", "step"},
        PlotLegends -> {"bag", "after a pop"}, ImageSize -> OptionValue[ImageSize], AspectRatio -> OptionValue[AspectRatio]]
]

(* 1 star, 2 set, 3 empty set, 4/5/6 the active element in state A/B/C *)
system4Row[c_Association] := ReplacePart[
    Replace[c["Elements"], {"*" -> 1, {} -> 3, _List -> 2}, {1}],
    If[c["Active"] < Length[c["Elements"]], {c["Active"] + 1 -> (c["State"] /. {"A" -> 4, "B" -> 5, "C" -> 6})}, {}]]

$stateColors = {RGBColor[0.85, 0.2, 0.2], RGBColor[0.2, 0.45, 0.85], RGBColor[0.95, 0.65, 0.1]};

System4EvolutionPlot[s4_Association, n_Integer?NonNegative, opts : OptionsPattern[evolutionPlot]] := Module[
    {run, k},
    {run, k} = sampledRun[system4Step, s4, n, OptionValue["MaxRows"]];
    ArrayPlot[PadRight[system4Row /@ run, Automatic, 0],
        ColorRules -> {0 -> White, 1 -> GrayLevel[0.15], 2 -> GrayLevel[0.6], 3 -> GrayLevel[0.9],
            4 -> $stateColors[[1]], 5 -> $stateColors[[2]], 6 -> $stateColors[[3]]},
        FrameTicks -> rowTicks[k, Length[run]], Frame -> True,
        ImageSize -> OptionValue[ImageSize], AspectRatio -> OptionValue[AspectRatio]]
]

(* cells 0, 1, 2 and the active cell as 3 + the index of the state *)
tapeRow[left_, head_, right_, stateIndex_] := Join[Reverse[left], {3 + stateIndex}, right]

tapePlot[rows_, k_, size_, aspect_] := ArrayPlot[PadRight[rows, Automatic, 0],
    ColorRules -> {0 -> White, 1 -> GrayLevel[0.65], 2 -> GrayLevel[0.15],
        4 -> $stateColors[[1]], 5 -> $stateColors[[2]], 6 -> $stateColors[[3]]},
    FrameTicks -> rowTicks[k, Length[rows]], Frame -> True, ImageSize -> size, AspectRatio -> aspect]

System3EvolutionPlot[s3_Association, n_Integer?NonNegative, opts : OptionsPattern[evolutionPlot]] := Module[
    {run, k},
    {run, k} = sampledRun[system3Step, s3, n, OptionValue["MaxRows"]];
    tapePlot[tapeRow[#["Left"], #["Head"], #["Right"], #["State"] /. {"A" -> 1, "B" -> 2, "C" -> 3}] & /@ run,
        k, OptionValue[ImageSize], OptionValue[AspectRatio]]
]

Wolfram23EvolutionPlot[{q0_Integer, l0_List, h0_Integer, r0_List}, n_Integer?NonNegative,
        opts : OptionsPattern[evolutionPlot]] := Module[
    {tape = Join[Reverse[l0], {h0}, r0], pos = Length[l0] + 1, q = q0, t = 0, rule, rows, k, row, shift = 0},
    k = Max[1, Ceiling[n/OptionValue["MaxRows"]]];
    (* rows hold absolute positions: a cell added at the left end shifts the earlier rows *)
    row[] := {shift, ReplacePart[tape, pos -> 3 + q]};
    rows = {row[]};
    While[t < n,
        rule = $wolfram23Table[[q, tape[[pos]] + 1]];
        tape[[pos]] = rule[[2]]; q = rule[[1]]; pos += rule[[3]];
        If[pos == 0, PrependTo[tape, 0]; pos = 1; shift++];
        If[pos > Length[tape], AppendTo[tape, 0]];
        t++;
        If[Mod[t, k] == 0, AppendTo[rows, row[]]]];
    tapePlot[Join[ConstantArray[0, shift - #[[1]]], #[[2]]] & /@ rows, k, OptionValue[ImageSize], OptionValue[AspectRatio]]
]

End[]

EndPackage[]
