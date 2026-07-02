(* :Title: InductiveProofs *)

(* :Context: WolframInstitute`TuringMachine`InductiveProofs` *)

(* :Summary: Equational induction proofs (via the built-in FindEquationalProof) that a Turing
   machine's left-nested tape-configuration semantics matches its intended behavior, plus
   renderers for the resulting proof graphs and multiway rewrite clouds (equational, geodesic,
   token-event, rule-space) and a Z3Link-based layered layout engine for the induction proof
   graph. *)

(* Own subcontext, kept separate from the main WolframInstitute`TuringMachine` context so nothing
   defined here leaks into it. The parent context is declared as needed so the one symbol this file
   reads from it ($PvsNPStyles, defined in Visualizations.wl) still resolves. *)
BeginPackage["WolframInstitute`TuringMachine`InductiveProofs`", {"WolframInstitute`TuringMachine`"}]

DecodeTuringMachineRules::usage = "DecodeTuringMachineRules[tmNumber, s, k] decodes a Turing machine number into a list of symbolic transition rules {state, symbol} -> {newState, writeSymbol, direction}, using the qA/qB/... state symbols and s0/s1/... tape symbols."

RunMachine::usage = "RunMachine[rules, inputBits, maxSteps] runs a symbolic Turing machine (as decoded by DecodeTuringMachineRules) on inputBits and returns the list of left-nested tape configurations visited, one per step, up to maxSteps."

CompressToRunLength::usage = "CompressToRunLength[expr] compresses a left-nested tape configuration by collapsing maximal runs of s0/s1 cells into ones[n, ...]/zeros[n, ...] terms."

FindInductiveProof::usage = "FindInductiveProof[goal, axioms, t] proves ForAll[n, goal] by equational induction on n: it proves the base case (n -> zero) and the step case (n -> succ[n], with goal itself added as the induction hypothesis), each time-constrained to t seconds. Returns an Association with keys \"Valid\", \"Goal\", \"InductionVariable\", \"Axioms\", \"BaseGoal\", \"StepGoal\", \"IH\", \"BaseProof\", \"StepProof\"."

cachedProofFor::usage = "cachedProofFor[ru] returns the induction proof Association for Turing machine ru, from mergedProofFor, caching the result on disk (and in memory) alongside the notebook/package."

mergedProofFor::usage = "mergedProofFor[ru] derives the induction proof Association for Turing machine ru by trying, in order, the sweep, boundary, and scan-flip proof strategies, returning the first one that succeeds (or the last failure)."

RenderConfiguration::usage = "RenderConfiguration[expr, s, opts] renders a left-nested tape configuration expr (with s states) as a row of tape-cell graphics."

RenderEquation::usage = "RenderEquation[eqn, split, s, opts] renders an equation between two tape configurations as tape-cell rows either side of an '='. split -> True returns {lhs, \"=\", rhs} instead of a single combined Row."

RenderAxiomGrid::usage = "RenderAxiomGrid[axioms, s, opts] renders a list of ForAll-quantified axioms as a two-column grid of rendered equations."

RenderUniversalGoal::usage = "RenderUniversalGoal[var, eqn, opts] renders ForAll[var, eqn] as a quantifier glyph followed by the rendered equation."

ShowTapeConfiguration::usage = "ShowTapeConfiguration[tape, headPos, state, opts] renders a tape (as a list of cells) with the head/state inserted at headPos, run-length compressed by default.
ShowTapeConfiguration[config, opts] renders an already-built left-nested configuration directly."

multiwaySystemFor::usage = "multiwaySystemFor[ru] bundles the axioms, induction hypothesis, derived-lemma rows, and base/step seed equations for Turing machine ru, as used by the multiway panel functions (IslandsPanel, StatementPanel, TokenEventPanel, SettingsPanel, RuleSpacePanel)."

multiwaySubProofCones::usage = "multiwaySubProofCones[ru, opts] builds a bounded multiway rewrite cloud ('cone') around each sub-proof (base case, step case, and any grafted derived-lemma cases) of machine ru's induction proof. Returns an Association with keys \"ProofGraph\", \"CaseList\", \"Cones\"."

multiwayDistance::usage = "multiwayDistance[lhsE, rhsE, axioms, steps, wellFormed] evolves a multiway rewrite cloud seeded at {lhsE, rhsE} for steps generations and returns the graph distance between them (Infinity if disconnected within that many steps)."

MultiwayEquationalGraph::usage = "MultiwayEquationalGraph[axioms, initExprsRaw, steps, style, opts] evolves a multiway equational-rewrite cloud from initExprsRaw for steps generations and renders it as a graph, highlighting the equational proof path (if any) between the seed expressions.
Options: \"CriticalPairs\" (False), \"VertexLabels\" (None), \"WellFormedOnly\" (True), \"ArrowSize\" (Automatic), \"Oriented\" (False), \"Ordering\" (\"LeafCount\"), \"CalloutMaxWidth\" (240)."

MultiwayGeodesicGraph::usage = "MultiwayGeodesicGraph[axioms, initExprsRaw, steps, opts] evolves a multiway rewrite cloud from initExprsRaw for steps generations and renders it with the geodesic path between the seeds (or to True) highlighted.
Options: \"CriticalPairs\" (False), \"WellFormedOnly\" (True), \"ShowLength\" (False), \"VertexLabels\" (Automatic), \"Oriented\" (False), \"Ordering\" (\"LeafCount\"), \"CloudUndirected\" (False), \"ArrowSize\" (Automatic), \"CalloutMaxWidth\" (240)."

MultiwayTokenEventGraph::usage = "MultiwayTokenEventGraph[axioms, initExprsRaw, steps, opts] evolves a multiway rewrite cloud in token-event form (state -> event -> state, with an axiom vertex feeding each event) and renders it, highlighting the proof path between the seed expressions.
Options: \"WellFormedOnly\" (True), \"Labeled\" (False), \"CollapseAxioms\" (False), \"ShowAxioms\" (True), \"SizeByLeafCount\" (False), \"HighlightStyle\" (\"Red\"), \"WashOpacity\" (0.5), \"FadeOpacity\" (0.13), \"PinProof\" (False), \"ProofLayout\" (\"LayeredDigraphEmbedding\"), \"PinCoords\" ({}), \"MaxStates\" (Infinity), \"VertexScale\" (1), \"ArrowSize\" (0.011), \"Oriented\" (False), \"Ordering\" (\"LeafCount\"), \"CriticalPairs\" (False)."

proofGraph::usage = "proofGraph[ru, mode, opts] renders the induction proof graph for Turing machine ru ('Labelled' or 'Unlabelled' mode) using the Z3 layered layout engine by default; 'Layout' -> a GraphLayout spec instead uses Wolfram's own layout.
proofGraph[p, mode, opts] renders the induction proof graph for an already-built proof Association p (as returned by cachedProofFor / mergedProofFor / FindInductiveProof)."

IslandsPanel::usage = "IslandsPanel[ru, case, opts] renders the multiway equational-rewrite cloud for one case ('Base', 'Step', 'StepRows', or 'CP') of Turing machine ru's induction proof."

StatementPanel::usage = "StatementPanel[ru, k, opts] renders the multiway geodesic graph between the base or step seed equations of Turing machine ru, seeded with the axioms plus the first k derived-lemma rows."

TokenEventPanel::usage = "TokenEventPanel[ru, k, opts] renders the multiway token-event graph for Turing machine ru's base or step case, seeded with the axioms plus the first k derived-lemma rows."

MultiwayBothPanel::usage = "MultiwayBothPanel[ru, opts] renders side-by-side faded multiway token-event cones for the base and step cases of Turing machine ru, captioned with the induction rule."

SettingsPanel::usage = "SettingsPanel[ru, opts] renders the multiway geodesic graph for Turing machine ru's full step case (axioms, induction hypothesis, and all derived-lemma rows), useful for tuning panel options before use elsewhere."

RuleSpacePanel::usage = "RuleSpacePanel[ru, opts] renders the MultiwayRuleGraph (superposition/critical-pair rule space) of Turing machine ru's axioms plus induction hypothesis."

inductionProofGraph

multiwayCloudOverlap

MultiwayRuleGraph

MultiwayInductiveProofPanel

$InductiveProofColors::usage = "$InductiveProofColors is the association of every colour used by the proof-graph and multiway renderers, keyed by role (e.g. \"AxiomBackground\", \"TheoremFrame\", \"EquationalEdge\"). Each value is a LightDarkSwitched[light, dark] pair so the graphics adapt to the notebook theme."

(* Proof-term vocabulary: the alphabet of tape configurations and proof equations (state symbols,
   tape-cell symbols, run/sequence constructors, boundary markers, Peano numerals, and the free
   variables). Declared as public symbols of THIS context (not the Private one) for two reasons:
   1. Cached proofs on disk bake in each symbol's full context, so pinning the vocabulary to a
      stable context (WolframInstitute`TuringMachine`InductiveProofs`) keeps old caches valid
      across reloads instead of silently mismatching a freshly-built cloud and disconnecting it.
   2. It lets these terms be typed and inspected directly from a notebook while resolving to the
      SAME symbols the package uses.
   ClearAll runs on every load so a stray notebook assignment to one of these names cannot corrupt
   the vocabulary. The Formal variables the code also uses (\[FormalA] etc.) are already System`
   symbols, so they are stable without help. *)
ClearAll[
    qA, qB, qC, qD, qH,
    s0, s1, s2, s3,
    seq, ones, zeros, onesRun, zerosRun,
    bnd, end, unbnd, unbndMark,
    zero, succ,
    segVar, variableCellBox, haltConfig,
    x, y, m, n
]

Begin["`Private`"]

(* Every self-memoizing function (f[x_] := f[x] = ...) accumulates one DownValue per distinct
   argument it has ever been called with; redefining the general x_ pattern on reload does NOT
   drop those specific memoized entries, so a stale result (e.g. a cachedProofFor[453] computed
   before an axiom-encoding change) silently survives a Get of this file in a live kernel and
   feeds inconsistent data to everything downstream. ClearAll here wipes both the memoized
   instances and the explicit cache Associations before anything below redefines them, so every
   reload of this file starts from a clean slate regardless of what a previous load left behind. *)
ClearAll[cachedProofFor, multiwaySystemFor, stateIndicatorPrimitives]

ClearAll[$rasterDimsCache, $boxBBoxCache, $z3LayoutMemo, $z3GraphicMemo]

(* === External styling (paclet) === *)

$turingMachineColorRules = $PvsNPStyles["TuringMachineColorRules"]

(* Z3Link is only needed by the layout engine's Z3Real/Z3Bool/Z3Optimize solve (the induction
   proofs themselves use the built-in FindEquationalProof, no Z3Link required), so load it lazily
   on first layout solve instead of at package-load time. *)
$z3LinkLoaded = False

ensureZ3Link[] := If[! TrueQ[$z3LinkLoaded], Needs["WolframInstitute`Z3Link`"]; $z3LinkLoaded = True]

(* === TM decoding (machine number -> transition rules) === *)

$StateSymbolMap = {1 -> qA, 2 -> qB, 3 -> qC, 4 -> qD}

$TapeSymbolMap = {0 -> s0, 1 -> s1, 2 -> s2, 3 -> s3}

DecodeTuringMachineRules[tmNumber_Integer, s_Integer, k_Integer] := Module[{raw, stateMap, symMap},
    raw = ResourceFunction["TuringMachineFromNumber"][tmNumber, s, k];
    stateMap = Table[i -> $StateSymbolMap[[i, 2]], {i, 1, s}];
    symMap = Table[i -> $TapeSymbolMap[[i + 1, 2]], {i, 0, k - 1}];
    Map[
        Function[rule,
            Module[{st, rd, ns, wr, d},
                st = rule[[1, 1]] /. stateMap;
                rd = rule[[1, 2]] /. symMap;
                ns = rule[[2, 1]] /. stateMap;
                wr = rule[[2, 2]] /. symMap;
                d = rule[[2, 3]];
                {st, rd} -> {ns, wr, d}
            ]
        ]
        ,
        raw
    ]
]

(* === Left-nested tape terms === *)

buildConfiguration[cellList_List] := Fold[seq[#1, #2]&, end, Append[cellList, bnd]]

flattenSequence[seq[a_, b_]] := Join[flattenSequence[a], flattenSequence[b]]

flattenSequence[c_] := {c}

CompressToRunLength[expr_] := Module[{
    parts = Map[
        With[{n = Length[#], sym = First[#]},
            If[n == 1, sym, If[sym === s1, ones[n], zeros[n]]]
        ]&
        ,
        Split[flattenSequence[expr], #1 === #2 && MatchQ[#1, s0 | s1]&]
    ]
},
    Fold[seq, First[parts], Rest[parts]]
]

encodeTransitionAxioms[rules_] := Map[
    Function[rule,
        Module[{st, rd, ns, wr, dir},
            {st, rd} = rule[[1]];
            {ns, wr, dir} = rule[[2]];
            If[ dir == -1,
                ForAll[x, seq[seq[x, rd], st] == seq[seq[x, ns], wr]]
                ,
                ForAll[{y, x}, seq[seq[seq[x, rd], st], y] == seq[seq[seq[x, wr], y], ns]]
            ]
        ]
    ]
    ,
    rules
]

onesRunDefinitions = {ForAll[y, ones[zero, y] == y], ForAll[{m, y}, ones[succ[m], y] == seq[ones[m, y], s1]]}

zerosRunDefinitions = {ForAll[y, zeros[zero, y] == y], ForAll[{m, y}, zeros[succ[m], y] == seq[zeros[m, y], s0]]}

unboundAxiom = ForAll[x, unbnd[seq[x, bnd]] == x]

trimTrailingZeros[cells_, minLength_] := NestWhile[Most, cells, Length[#] > minLength && Last[#] === s0&]

RunMachine[rules_, inputBits_, maxSteps_ : 200] := Module[{step, configOf, states},
    step[{tape_, head_, state_, "run"}] := Module[{paddedTape, symbol, transition},
        paddedTape = If[head > Length[tape], Append[tape, s0], tape];
        If[head < 1, Return[{paddedTape, head, state, "stuck"}]];
        symbol = paddedTape[[head]];
        transition = SelectFirst[rules, #[[1]] === {state, symbol}&, None];
        If[transition === None, Return[{paddedTape, head, state, "stuck"}]];
        With[{nextState = transition[[2, 1]], write = transition[[2, 2]], direction = transition[[2, 3]]},
            With[{nextHead = head - direction},
                {ReplacePart[paddedTape, head -> write], nextHead, nextState, If[nextHead < 1, "halt", "run"]}
            ]
        ]
    ];
    configOf[{tape_, _, _, "halt"}] := buildConfiguration[Reverse[Join[{qH}, trimTrailingZeros[tape, 1]]]];
    configOf[{tape_, head_, state_, _}] := buildConfiguration[Reverse[trimTrailingZeros[Join[Take[tape, head - 1], {state}, Drop[tape, head - 1]], head + 1]]];
    states = NestWhileList[step, {Join[inputBits, {s0, s0, s0}], 1, qA, "run"}, #[[4]] === "run"&, 1, maxSteps];
    configOf /@ If[Last[states][[4]] === "stuck", Most[states], states]
]

(* === Shared vocabulary (defined once, referenced everywhere) === *)

$proofVariables = {x, y, m, n, , , , , , , , , , }

$formalVariables = {, , , }

$ruleCanonicalVariables = {, , , , , }

canonicalizeVariables[e_] := Module[{vs = DeleteDuplicates[Cases[e, s_Symbol /; MemberQ[$proofVariables, s], {0, Infinity}]]},
    e /. Thread[vs -> Table[Symbol["cv" <> ToString[j]], {j, Length[vs]}]]
]

forAllBody[axiom_] := axiom //. ForAll[_, body_] :> body

forAllVariables[axiom_] := Flatten[Map[First, Cases[axiom, _ForAll, {0, Infinity}]]]

edgeTag[e_] := If[Length[List @@ e] >= 3, (List @@ e)[[3]], None]

graphOption[g_, opt_] := Options[g, opt][[1, 2]]

noVertexLabels[verts_] := VertexLabels -> Map[# -> None&, verts]

$emptyRunSimplification = {ones[zero, z_] :> z, zeros[zero, z_] :> z}

$states = {qA, qB, qC, qD, qH}

wellFormedQ[t_] := If[ MatchQ[t, _Equal],
    Count[t[[1]], Alternatives @@ $states, {0, Infinity}] <= 1
    &&
    Count[t[[2]], Alternatives @@ $states, {0, Infinity}] <= 1
    ,
    Count[t, Alternatives @@ $states, {0, Infinity}] <= 1
]

(* === Color palette === *)

(* Every colour used by the proof-graph and multiway renderers, in one place. Each entry is
   LightDarkSwitched[light, dark] so the graphics adapt to the notebook theme; the dark variant is
   derived from the light one by keeping hue and saturation and inverting brightness (backgrounds
   go from a pale panel to a muted dark one; dark strokes/text are brightened to stay legible). *)
$InductiveProofColors = <|
    "CellBackground" -> LightDarkSwitched[GrayLevel[0.98], GrayLevel[0.162]],
    "CellEdge" -> LightDarkSwitched[GrayLevel[0.5, 0.4], GrayLevel[0.55, 0.4]],
    "AxiomHue" -> LightDarkSwitched[Hue[0.19, 0.87, 0.7], Hue[0.19, 0.8, 0.75]],
    "AxiomBackground" -> LightDarkSwitched[Lighter[Hue[0.19, 0.87, 0.7], 0.85], Hue[0.19, 0.096, 0.164]],
    "AxiomText" -> LightDarkSwitched[RGBColor[0.100, 0.228, 0.], Hue[0.26, 1., 0.575]],
    "AxiomFrame" -> LightDarkSwitched[RGBColor[0.1907616, 0.372, 0.04836], Hue[0.26, 0.8, 0.422]],
    "AxiomVertexEdge" -> LightDarkSwitched[RGBColor[0.41, 0.5, 0], Hue[0.197, 0.92, 0.55]],
    "TheoremHue" -> LightDarkSwitched[Hue[0.49, 0.45, 0.87], Hue[0.49, 0.414, 0.92]],
    "TheoremBackground" -> LightDarkSwitched[Lighter[Hue[0.49, 0.45, 0.87], 0.85], Hue[0.49, 0.06, 0.162]],
    "TheoremText" -> LightDarkSwitched[RGBColor[0.024, 0.222, 0.222], Hue[0.5, 0.892, 0.572]],
    "TheoremFrame" -> LightDarkSwitched[RGBColor[0.1035, 0.39537, 0.414], Hue[0.51, 0.69, 0.464]],
    "InductionFill" -> LightDarkSwitched[RGBColor[0.96, 0.935, 0.9875], Hue[0.746, 0.053, 0.161]],
    "InductionStroke" -> LightDarkSwitched[RGBColor[0.45, 0.26, 0.65], Hue[0.748, 0.552, 0.7]],
    "InductionVertexEdge" -> LightDarkSwitched[RGBColor[0.8625, 0.815, 0.9125], RGBColor[0.8755, 0.8284, 0.925]],
    "InductionRuleBackground" -> LightDarkSwitched[Lighter[Hue[0.14, 0.61, 0.98], 0.85], Hue[0.14, 0.09, 0.16]],
    "DefaultEventFill" -> LightDarkSwitched[Hue[0.1, 0.85, 0.97], Hue[0.1, 0.782, 1.]],
    "DefaultEventStroke" -> LightDarkSwitched[Hue[0.07, 1, 0.5], Hue[0.07, 0.92, 0.55]],
    "CriticalPairEventFill" -> LightDarkSwitched[RGBColor[0.9215686, 0.4941176, 0.4313725], Hue[0.021, 0.489, 0.972]],
    "CriticalPairEventStroke" -> LightDarkSwitched[RGBColor[0.465, 0.124, 0.0695], Hue[0.023, 0.782, 0.515]],
    "EquationalEdge" -> LightDarkSwitched[Hue[0.1, 0.34, 0.49], Hue[0.1, 0.313, 0.54]],
    "PathHighlight" -> LightDarkSwitched[RGBColor[1., 0.722, 0.220], Hue[0.107, 0.718, 1.]],
    "PathHighlightBackground" -> LightDarkSwitched[Lighter[RGBColor[1., 0.722, 0.220], 0.85], Hue[0.107, 0.15, 0.18]],
    "TokenEventAxiomHue" -> LightDarkSwitched[Hue[0.26, 0.45, 0.87], Hue[0.26, 0.414, 0.92]],
    "IdentityFill" -> LightDarkSwitched[GrayLevel[0.25], GrayLevel[0.587]],
    "IdentityStroke" -> LightDarkSwitched[GrayLevel[0.1], GrayLevel[0.505]],
    "IdentityBackground" -> LightDarkSwitched[GrayLevel[0.93], GrayLevel[0.167]],
    "CalloutConnector" -> LightDarkSwitched[GrayLevel[0.125], GrayLevel[0.519]],
    "FallbackFrame" -> LightDarkSwitched[GrayLevel[0.4], GrayLevel[0.45]],
    "StateIndicatorBackground" -> LightDarkSwitched[GrayLevel[0.92], GrayLevel[0.168]],
    "StateIndicatorFill" -> LightDarkSwitched[RGBColor[0.27, 0.5, 0.72], Hue[0.581, 0.575, 0.77]],
    "StateIndicatorEdge" -> LightDarkSwitched[GrayLevel[0.45], GrayLevel[0.5]],
    "VariableCellEdge" -> LightDarkSwitched[GrayLevel[0.55], GrayLevel[0.6]],
    "LabelText" -> LightDarkSwitched[GrayLevel[0.], GrayLevel[0.92]]
|>

(* apply a numeric colour-space function through a LightDarkSwitched value by mapping over both
   branches, so colour math (ColorConvert, Blend, Lighter, Darker) keeps working once a colour
   becomes theme-dependent; a plain (non-switched) colour is passed through unchanged. *)
switchedColor[f_, LightDarkSwitched[l_, d_]] := LightDarkSwitched[f[l], f[d]]

switchedColor[f_, c_] := f[c]

(* === Flat rendering === *)

$cellSize = 14; $stateCount = 2

$cellBackground = $InductiveProofColors["CellBackground"]

$graphCellSize = 9

$cellFontScale = 6/7

(* === L0: shared text/arrow style context === *)

(* Block-scoped, one place, every graph reads these. All default to Automatic/current
   behaviour so nothing regresses. *)

$textFontSize = Automatic; (* absolute equation-cell font (pt); Automatic = $cellFontScale*$cellSize *)

$traditionalForm = True; (* TraditionalForm on variables, exponents, quantifier var *)

$quantifierTraditional = True; (* the forall bound variable in TraditionalForm *)

$arrowSize = Automatic; (* base arrowhead size (plot fraction); Automatic = 0.013 *)

$arrowScalesWithThickness = True; (* arrowhead grows with edge AbsoluteThickness *)

$scriptRaise = 0.42; (* run-length exponent lift (baseline shifts) *)

$centerOnEquals = True; (* centre the box on the main equation line so a superscript is balanced by invisible space below;
   False = ink-centre *)

$vertexScale = 1; (* multiplies the Unlabelled-mode circle diameters *)

(* the one form decision: a form-sensitive leaf (variable, exponent, quantifier var) in the given
   form. trad uses the equation flag; the quantifier var uses its own flag. Box-level sites
   (raised scripts, the quantifier subscript) take formBoxes; live sites take trad. *)

formWrap[e_, useTrad_] := If[TrueQ[useTrad], TraditionalForm[e], e]

formBoxes[e_, useTrad_] := ToBoxes[e, If[TrueQ[useTrad], TraditionalForm, StandardForm]]

trad[e_] := formWrap[e, $traditionalForm]

arrowheadsFor[thickness_] := Arrowheads[
    Replace[$arrowSize, Automatic :> 0.013]
    *
    If[TrueQ[$arrowScalesWithThickness], Max[0.45, thickness / 2.4], 1]
]

(* the single standard option set; every public renderer accepts exactly these. "BoxPadding" -> n
   sets both directions; -> {h, v} sets them separately. *)

$renderStyleOptions = {
    "FontSize" -> Automatic,
    "CellSize" -> Automatic,
    "FontScale" -> Automatic,
    "BoxPadding" -> Automatic,
    "QuantifierSize" -> Automatic,
    "TraditionalForm" -> Automatic,
    "QuantifierTraditional" -> Automatic,
    "ScriptRaise" -> Automatic,
    "CenterOnEquals" -> Automatic,
    "ArrowSize" -> Automatic,
    "ArrowScalesWithThickness" -> Automatic,
    "VertexScale" -> Automatic,
    "BorderThickness" -> Automatic,
    "CellBorderThickness" -> Automatic,
    "InductionEdgeThickness" -> Automatic,
    "ArrowGap" -> Automatic,
    "BoxArrowGap" -> Automatic,
    "CircleArrowGap" -> Automatic,
    "DotSpacing" -> Automatic,
    "BorderColor" -> Automatic,
    "QuantifierNudge" -> Automatic,
    "ConclusionGap" -> Automatic,
    "RoundRouting" -> Automatic,
    "AxiomRows" -> Automatic,
    "IHAboveCircle" -> Automatic,
    "AxiomGap" -> Automatic,
    "AxiomSide" -> Automatic,
    "Layout" -> Automatic
}

SetAttributes[withRenderStyle, HoldAll]

withRenderStyle[defCell_, opts_, body_] := Module[{o = opts, gv2, tfs, cs, ag},
    gv2[name_] := OptionValue[$renderStyleOptions, o, name];
    tfs = Replace[gv2["FontSize"], Automatic :> $textFontSize];
    cs = Replace[gv2["CellSize"], Automatic :> If[NumberQ[tfs], Round[tfs / $cellFontScale], defCell]];
    ag = Replace[gv2["ArrowGap"], Automatic :> $arrowGap]; (* the fallback gap for both ends *)
    Block[{
        $cellSize = cs,
        $graphCellSize = cs,
        $textFontSize = tfs,
        $cellFontScale = Replace[gv2["FontScale"], Automatic :> $cellFontScale],
        $boxPadding = Replace[gv2["BoxPadding"], {Automatic :> $boxPadding, n_ ? NumericQ :> {n, n}}],
        $quantifierSize = Replace[gv2["QuantifierSize"], Automatic :> $quantifierSize],
        $traditionalForm = Replace[gv2["TraditionalForm"], Automatic :> $traditionalForm],
        $quantifierTraditional = Replace[gv2["QuantifierTraditional"], Automatic :> $quantifierTraditional],
        $scriptRaise = Replace[gv2["ScriptRaise"], Automatic :> $scriptRaise],
        $centerOnEquals = Replace[gv2["CenterOnEquals"], Automatic :> $centerOnEquals],
        $arrowSize = Replace[gv2["ArrowSize"], Automatic :> $arrowSize],
        $arrowScalesWithThickness = Replace[gv2["ArrowScalesWithThickness"], Automatic :> $arrowScalesWithThickness],
        $vertexScale = Replace[gv2["VertexScale"], Automatic :> $vertexScale],
        $boxEdgeThickness = Replace[gv2["BorderThickness"], Automatic :> $boxEdgeThickness],
        $cellEdgeThickness = Replace[gv2["CellBorderThickness"], Automatic :> $cellEdgeThickness],
        $inductionEdgeThickness = Replace[gv2["InductionEdgeThickness"], Automatic :> $inductionEdgeThickness],
        $arrowGap = ag,
        $boxArrowGap = Replace[gv2["BoxArrowGap"], Automatic :> ag],
        $circleArrowGap = Replace[gv2["CircleArrowGap"], Automatic :> ag],
        $cellSeparatorGap = Replace[gv2["DotSpacing"], Automatic :> $cellSeparatorGap],
        $quantifierNudge = Replace[gv2["QuantifierNudge"], Automatic :> $quantifierNudge],
        $cellEdgeColor = Replace[gv2["BorderColor"], Automatic :> $cellEdgeColor],
        $conclusionGap = Replace[gv2["ConclusionGap"], Automatic :> $conclusionGap],
        $roundRouting = Replace[gv2["RoundRouting"], Automatic :> $roundRouting],
        $axiomRows = Replace[gv2["AxiomRows"], Automatic :> $axiomRows],
        $ihAboveCircle = Replace[gv2["IHAboveCircle"], Automatic :> $ihAboveCircle],
        $axiomGap = Replace[gv2["AxiomGap"], Automatic :> $axiomGap],
        $axiomSide = Replace[gv2["AxiomSide"], Automatic :> $axiomSide]
    },
        body
    ]
]

$cellEdgeColor = $InductiveProofColors["CellEdge"]; (* matches ArrayPlot's default Mesh style *)

$cellEdgeThickness = 0.1; (* the s0/s1 tape-cell square borders; independent of the vertex box *)

$quantifierNudge = 0; (* vertical shift of the forall glyph (pt), + raises *)

cellEdge[] := EdgeForm[{$cellEdgeColor, AbsoluteThickness[$cellEdgeThickness]}]

squareCell[fill_] := Graphics[
    {fill, cellEdge[], Rectangle[{-0.5, -0.5}, {0.5, 0.5}]},
    PlotRange -> {{-0.55, 0.55}, {-0.55, 0.55}},
    PlotRangePadding -> None,
    ImageSize -> $cellSize
]

cellBox[1] := squareCell[1 /. $turingMachineColorRules]

cellBox[0] := squareCell[FaceForm[$cellBackground]]

grayCellBox[g_] := squareCell[GrayLevel[g]]

drawnStateIndicator[i_, n_] := {
    {$InductiveProofColors["StateIndicatorBackground"], Disk[{0, 0}, 0.46]},
    {$InductiveProofColors["StateIndicatorFill"], Disk[{0, 0}, 0.46, Pi / 2 - 2 Pi {i, i - 1} / n]},
    {$InductiveProofColors["StateIndicatorEdge"], AbsoluteThickness[0.6], Circle[{0, 0}, 0.46]}
}

(* the head-state dial: the FiniteStateIndicatorIcon resource when it resolves to real primitives,
   else a self-contained dial, so a head cell always renders. *)

stateIndicatorPrimitives[i_, n_] := stateIndicatorPrimitives[i, n] = Module[{r = Quiet @ Check[ResourceFunction["FiniteStateIndicatorIcon"][{0, 0}, {i, n}], $Failed]},
    Which[ 
        r === $Failed || StringContainsQ[ToString[r, InputForm], "FiniteStateIndicatorIcon"],
            drawnStateIndicator[i, n]
        ,
        MatchQ[r, _Graphics],
            First[r]
        ,
        True,
            r
    ]
]

stateIndicatorBox[i_] := Graphics[
    stateIndicatorPrimitives[i, $stateCount],
    PlotRange -> {{-0.5, 0.5}, {-0.55, 0.45}},
    PlotRangePadding -> None,
    ImageSize -> $cellSize
]

renderPeanoNumeral[zero] := 0

renderPeanoNumeral[s_succ] := With[{k = Count[s, succ, {0, Infinity}, Heads -> True], e = s //. succ[a_] :> a},
    If[e === zero, k, renderPeanoNumeral[e] + k]
]

renderPeanoNumeral[n] := m

renderPeanoNumeral[m] := m

renderPeanoNumeral[] := m

renderPeanoNumeral[] := m

renderPeanoNumeral[k_] := k

renderRunExponent[k_] := renderPeanoNumeral[k]

renderCell[s0] := cellBox[0]

renderCell[s1] := cellBox[1]

renderCell[qH] := grayCellBox[0.85]

renderCell[haltConfig] := grayCellBox[0.5]

renderCell[qA] := stateIndicatorBox[1]

renderCell[qB] := stateIndicatorBox[2]

renderCell[qC] := stateIndicatorBox[3]

renderCell[qD] := stateIndicatorBox[4]

renderCell[end] := "⊲"

renderCell[bnd] := "⊳"

(* the exponent, lifted by $scriptRaise above the native superscript position. The shift is on the
   exponent only, so the square base stays on the baseline and lines up with the plain cells and
   the dots: a plain Superscript, no invisible-mirror Subsuperscript. *)

raiseScript[e_] := RawBoxes[AdjustmentBox[formBoxes[e, $traditionalForm], BoxBaselineShift -> -$scriptRaise]]

runCell[base_, k_] := Superscript[base, raiseScript[renderRunExponent[k]]]

renderCell[onesRun[k_]] := runCell[cellBox[1], k]

renderCell[zerosRun[k_]] := runCell[cellBox[0], k]

renderCell[] := trad[x]

renderCell[] := trad[y]

renderCell[] := renderCell[]; renderCell[] := renderCell[]

renderCell[] := renderCell[]; renderCell[] := renderCell[]

renderCell[] := renderCell[]

renderCell[x] := renderCell[]; renderCell[y] := renderCell[]

renderCell[n] := renderPeanoNumeral[n]

renderCell[m] := renderPeanoNumeral[m]

renderCell[c_] := c

tapeCells[seq[a_, b_]] := Join[tapeCells[a], tapeCells[b]]

tapeCells[ones[k_, rest_]] := Append[tapeCells[rest], onesRun[k]]

tapeCells[zeros[k_, rest_]] := Append[tapeCells[rest], zerosRun[k]]

tapeCells[ones[k_]] := {onesRun[k]}

tapeCells[zeros[k_]] := {zerosRun[k]}

tapeCells[unbnd[t_]] := Replace[tapeCells[t], bnd -> unbndMark, {1}]

tapeCells[c_] := {c}

renderCell[unbndMark] := "⊳"

(* the centre-dot between cells is a Graphics disc, a peer of the square cells, with the same
   vertical PlotRange and the same ImageSize height, so it sits at the cell centre
   GEOMETRICALLY. A text "·" rides the font math axis, which the front end places differently
   from the graphic cells (so it reads too high there); a disc shares the cells' exact baseline.
   The graphic's width sets the horizontal spacing, in cell-size units, independent of the font. *)

$cellSeparatorGap = 0.62; (* total separator width, as a fraction of the cell size *)

$dotRadius = 0.07; (* centre-dot radius, as a fraction of the cell size *)

cellSeparator[] := With[{hw = $cellSeparatorGap 1.1 / 2},
    Graphics[
        {Disk[{0, 0}, $dotRadius]},
        PlotRange -> {{-hw, hw}, {-0.55, 0.55}},
        PlotRangePadding -> None,
        ImageSize -> {$cellSeparatorGap $cellSize, $cellSize}
    ]
]

$headStateSymbols = {qA, qB, qC, qD}

$tapeVariables = {x, y, , , , , , , }

renderCell[segVar] := trad[s]

variableCellBox /: renderCell[variableCellBox[_]] := Graphics[
    {
        FaceForm[$cellBackground],
        EdgeForm[$InductiveProofColors["VariableCellEdge"]],
        Rectangle[{-0.5, -0.5}, {0.5, 0.5}],
        Inset[trad[i], {0, 0.02}, Center, 0.85]
    }
    ,
    PlotRange -> {{-0.55, 0.55}, {-0.55, 0.55}}
    ,
    PlotRangePadding -> None
    ,
    ImageSize -> $cellSize
]

markTapeVariables[cells_List] := MapIndexed[
    Which[ 
        ! MemberQ[$tapeVariables, #1],
            #1
        ,
        #2[[1]] == 1,
            segVar
        ,
        True,
            variableCellBox[#1]
    ]&
    ,
    cells
]

$fontSize := Replace[$textFontSize, Automatic :> Round[$cellFontScale $cellSize]]

(* trad is applied only to the form-sensitive leaves (variables, exponents, quantifier var), never
   to the Row, the squares, or the separators, so TraditionalForm changes the maths without
   disturbing the dot spacing or bloating the graphics. *)

renderCellRow[cells_List] := Style[Row[Riffle[renderCell /@ markTapeVariables[cells], cellSeparator[]]], FontSize -> $fontSize]

Options[RenderConfiguration] = $renderStyleOptions

RenderConfiguration[expr_, s_Integer : 2, opts : OptionsPattern[]] := withRenderStyle[
    $cellSize
    ,
    {opts}
    ,
    Block[{$stateCount = s},
        renderCellRow[tapeCells[expr]]
    ]
]

Options[RenderEquation] = $renderStyleOptions

RenderEquation[eqn_, split : (True | False) : False, s_Integer : 2, opts : OptionsPattern[]] := withRenderStyle[
    $cellSize
    ,
    {opts}
    ,
    Module[{e = forAllBody[eqn], lhs, rhs, ok = False},
        If[ MatchQ[e, _HoldForm],
            Module[{pair = Replace[e, HoldForm[Equal[a_, b_]] :> {a, b}]},
                If[ ListQ[pair],
                    lhs = pair[[1]];
                    rhs = pair[[2]];
                    ok = True
                ]
            ]
        ];
        If[ ! ok && MatchQ[e, _Equal] && e =!= True,
            lhs = e[[1]];
            rhs = e[[2]];
            ok = True
        ];
        If[ ok,
            With[{sl = RenderConfiguration[lhs, s], sr = RenderConfiguration[rhs, s]},
                If[split, {sl, "=", sr}, Style[Row[{sl, "  ", "=", "  ", sr}], FontSize -> $fontSize]]
            ]
            ,
            RenderConfiguration[e /. HoldForm -> Identity, s]
        ]
    ]
]

Options[RenderAxiomGrid] = $renderStyleOptions

RenderAxiomGrid[axioms_List, opts : OptionsPattern[]] := RenderAxiomGrid[axioms, 2, opts]

RenderAxiomGrid[axioms_List, s_Integer, opts : OptionsPattern[]] := withRenderStyle[
    $cellSize,
    {opts},
    Grid[RenderEquation[#, True, s]& /@ axioms, Alignment -> {{Right, Center, Left}}, Spacings -> {1, 0.5}]
]

tapeForm /: MakeBoxes[tapeForm[equation_], form_] := ToBoxes[RenderEquation[equation], form]

$quantifierSize = Automatic

universalGoalGrid[var_, eqn_] := Module[{q, glyph},
    q = Replace[$quantifierSize, Automatic :> Round[1.5 $cellSize]];
    glyph = Style[Subscript["∀", RawBoxes[formBoxes[var, $quantifierTraditional]]], FontSize -> q];
    glyph = RawBoxes[AdjustmentBox[ToBoxes[glyph], BoxBaselineShift -> -$quantifierNudge]];
    Grid[
        {{glyph, tapeForm[eqn]}},
        Alignment -> {Automatic, Center},
        Spacings -> {0.5, 0},
        BaselinePosition -> Center
    ]
]

Unprotect[ForAll]

ForAll /: MakeBoxes[ForAll[var_, tapeForm[eqn_]], form_] := ToBoxes[universalGoalGrid[var, eqn], form]

Protect[ForAll]

Options[RenderUniversalGoal] = $renderStyleOptions

RenderUniversalGoal[var_, eqn_, opts : OptionsPattern[]] := withRenderStyle[$cellSize, {opts}, RawBoxes[ToBoxes[ForAll[var, tapeForm[eqn]]]]]

renderGraphEquation[eqn_] := Block[{$cellSize = $graphCellSize},
    RenderEquation[eqn]
]

renderGraphUniversalGoal[var_, eqn_] := Block[{$cellSize = $graphCellSize},
    RawBoxes[ToBoxes[RenderUniversalGoal[var, eqn]]]
]

Options[ShowTapeConfiguration] = Join[{"Compress" -> True, "ShowHead" -> True, "States" -> 2}, $renderStyleOptions]

ShowTapeConfiguration[tape_List, headPos_Integer, state_, opts : OptionsPattern[]] := Module[{
    showHead = TrueQ[OptionValue["ShowHead"]],
    compress = TrueQ[OptionValue["Compress"]],
    states = OptionValue["States"],
    cl,
    config
},
    cl = If[showHead, Join[Take[tape, headPos - 1], {state}, Drop[tape, headPos - 1]], tape];
    config = buildConfiguration[cl];
    If[compress, config = CompressToRunLength[config]];
    RenderConfiguration[config, states, FilterRules[{opts}, $renderStyleOptions]]
]

ShowTapeConfiguration[config_seq, opts : OptionsPattern[]] := RenderConfiguration[
    If[TrueQ[OptionValue["Compress"]], CompressToRunLength[config], config],
    OptionValue["States"],
    FilterRules[{opts}, $renderStyleOptions]
]

(* === Induction prover === *)

FindInductiveProof[goal_Equal, axioms_List, t_ : 30] := Module[{base, step},
    base = Quiet[TimeConstrained[FindEquationalProof[goal /. n -> zero, axioms], t, $TimedOut]];
    step = Quiet[TimeConstrained[FindEquationalProof[goal /. n -> succ[n], Join[axioms, {goal}]], t, $TimedOut]];
    <|
        "Valid" -> (MatchQ[base, _ProofObject] && MatchQ[step, _ProofObject]),
        "Goal" -> ForAll[n, goal],
        "InductionVariable" -> n,
        "Axioms" -> axioms,
        "BaseGoal" -> (goal /. n -> zero),
        "StepGoal" -> (goal /. n -> succ[n]),
        "IH" -> goal,
        "BaseProof" -> base,
        "StepProof" -> step
    |>
]

findInductionHypothesisAxiom[stepProof_ProofObject, ih_] := Module[{ds, labels, nRows, ihRev, axiomIndices, match},
    ds = stepProof["ProofDataset"];
    labels = Normal[Keys[ds]];
    nRows = Length[ds];
    ihRev = ih[[2]] == ih[[1]];
    axiomIndices = Select[Range[nRows], MatchQ[labels[[#]], {"Axiom", _}]&];
    match = SelectFirst[
        axiomIndices
        ,
        Module[{stmt = ReleaseHold[ds[#]["Statement"]]},
            stmt === ih || stmt === ihRev
        ]&
    ];
    If[MissingQ[match], None, labels[[match]]]
]

(* === Proof strategies (every behavioral lemma derived, never assumed) === *)

deriveCarry[tmAx_] := Module[{car = ForAll[x, seq[seq[x, s1], qA] == seq[seq[x, qA], s0]], po},
    If[MemberQ[tmAx, car], Return[<|"Axiom" -> car, "Proof" -> None|>]];
    po = Quiet[TimeConstrained[FindEquationalProof[car, tmAx], 30, $TimedOut]];
    If[MatchQ[po, _ProofObject], <|"Axiom" -> car, "Proof" -> po|>, $Failed]
]

withLemmas[p_, lems_Association] := If[AssociationQ[p], Append[p, "LemmaProofs" -> DeleteCases[lems, None]], p]

sweepProofFor[ru_] := Module[
    {rules = DecodeTuringMachineRules[ru, tmStatesFor[ru], 2], tmAx, sweepSt, sweepAx, abs, absPO, car}
    ,
    tmAx = encodeTransitionAxioms[rules];
    sweepSt = SelectFirst[
        {qB, qC, qD}
        ,
        Function[st,
            With[{r = Select[rules, #[[1, 1]] === st&]},
                Length[r] > 0 && AllTrue[r, #[[2, 2]] === #[[1, 2]]&]
            ]
        ]
    ];
    If[MissingQ[sweepSt], Return[$Failed]];
    sweepAx = ForAll[x, seq[x, sweepSt] == seq[x, qH]];
    car = deriveCarry[tmAx];
    If[car === $Failed, Return[$Failed]];
    abs = ForAll[x, seq[seq[x, s0], qA] == seq[seq[x, qH], s1]];
    absPO = Quiet[TimeConstrained[FindEquationalProof[abs, Join[tmAx, {sweepAx}]], 30, $TimedOut]];
    If[! MatchQ[absPO, _ProofObject], Return[$Failed]];
    withLemmas[
        FindInductiveProof[
            seq[ones[n, seq[x, s0]], qA] == zeros[n, seq[seq[x, qH], s1]],
            Join[{car["Axiom"], abs}, onesRunDefinitions, zerosRunDefinitions],
            30
        ]
        ,
        <|"Carry" -> car["Proof"], "Absorb" -> absPO|>
    ]
]

boundaryProofFor[ru_] := Module[{
    rules = DecodeTuringMachineRules[ru, tmStatesFor[ru], 2],
    states,
    tmAx,
    boundaryAxioms,
    abs,
    absPO,
    car
},
    states = DeleteDuplicates[rules[[All, 1, 1]]];
    tmAx = encodeTransitionAxioms[rules];
    boundaryAxioms = Map[ForAll[x, seq[seq[x, bnd], #] == seq[x, bnd]]&, states];
    car = deriveCarry[tmAx];
    If[car === $Failed, Return[$Failed]];
    abs = ForAll[x, seq[seq[seq[x, s0], qA], bnd] == seq[seq[x, s1], bnd]];
    absPO = Quiet[TimeConstrained[FindEquationalProof[abs, Join[tmAx, boundaryAxioms]], 30, $TimedOut]];
    If[! MatchQ[absPO, _ProofObject], Return[$Failed]];
    withLemmas[
        FindInductiveProof[
            seq[seq[ones[n, seq[x, s0]], qA], bnd] == seq[zeros[n, seq[x, s1]], bnd],
            Join[{car["Axiom"], abs}, onesRunDefinitions, zerosRunDefinitions, {unboundAxiom}],
            60
        ]
        ,
        <|"Carry" -> car["Proof"], "Absorb" -> absPO|>
    ]
]

scanFlipProofFor[ru_] := Module[{
    rules = DecodeTuringMachineRules[ru, tmStatesFor[ru], 2],
    states,
    tmAx,
    boundaryAxioms,
    goalD,
    goalL1,
    goalG,
    pD,
    pL1,
    pG,
    pMain
},
    states = DeleteDuplicates[rules[[All, 1, 1]]];
    tmAx = encodeTransitionAxioms[rules];
    boundaryAxioms = Map[ForAll[x, seq[seq[x, bnd], #] == seq[x, bnd]]&, states];
    goalD = ones[succ[n], y] == ones[n, seq[y, s1]];
    goalL1 = seq[ones[n, x], qA] == ones[n, seq[x, qA]];
    goalG = ones[n, seq[seq[x, s1], qB]] == seq[seq[zeros[n, x], s1], qB];
    pD = FindInductiveProof[goalD, onesRunDefinitions, 30];
    pL1 = FindInductiveProof[goalL1, Join[tmAx, onesRunDefinitions], 30];
    pG = FindInductiveProof[goalG, Join[tmAx, onesRunDefinitions, zerosRunDefinitions], 30];
    If[! (TrueQ[pD["Valid"]] && TrueQ[pL1["Valid"]] && TrueQ[pG["Valid"]]), Return[$Failed]];
    pMain = FindInductiveProof[
        seq[seq[ones[n, seq[x, s0]], qA], bnd] == seq[zeros[n, seq[x, s1]], bnd]
        ,
        Join[
            {ForAll[{n, y}, Evaluate[goalD]], ForAll[{n, x}, Evaluate[goalL1]], ForAll[{n, x}, Evaluate[goalG]]},
            tmAx, boundaryAxioms, onesRunDefinitions, zerosRunDefinitions, {unboundAxiom}
        ]
        ,
        120
    ];
    If[ AssociationQ[pMain],
        Append[pMain, "LemmaProofs" -> <|"TailPeel" -> pD, "Scan" -> pL1, "Flip" -> pG|>]
        ,
        pMain
    ]
]

mergedProofFor[ru_] := Module[{p = sweepProofFor[ru]},
    If[! (AssociationQ[p] && TrueQ[p["Valid"]]), p = boundaryProofFor[ru]];
    If[! (AssociationQ[p] && TrueQ[p["Valid"]]), p = scanFlipProofFor[ru]];
    p
]

$proofCacheDir = Which[ 
    StringQ[Quiet[NotebookDirectory[]]],
        NotebookDirectory[]
    ,
    $InputFileName =!= "",
        DirectoryName[$InputFileName]
    ,
    True,
        Directory[]
]

cachedProofFor[ru_] := cachedProofFor[ru] = Module[{f = FileNameJoin[{$proofCacheDir, "proofcache_" <> ToString[ru] <> ".mx"}], p},
    If[ FileExistsQ[f],
        Import[f]
        ,
        p = mergedProofFor[ru];
        Export[f, p];
        p
    ]
]

(* === Per-machine axiom and proof accessors (proofs come from the cache) === *)

transitionAxiomsFor[ru_] := encodeTransitionAxioms[DecodeTuringMachineRules[ru, 2, 2]]

boundaryAxiomsFor[ru_] := Map[
    ForAll[x, seq[seq[x, bnd], #] == seq[x, bnd]]&,
    DeleteDuplicates[DecodeTuringMachineRules[ru, 2, 2][[All, 1, 1]]]
]

goalFor[ru_] := cachedProofFor[ru]["Goal"]

derivedAxiomsFor[ru_] := Complement[
    cachedProofFor[ru]["Axioms"],
    transitionAxiomsFor[ru],
    boundaryAxiomsFor[ru],
    onesRunDefinitions,
    zerosRunDefinitions,
    {unboundAxiom}
]

proofInputRole[axiom_, ru_] := Which[ 
    MemberQ[transitionAxiomsFor[ru], axiom],
        "raw transition"
    ,
    MemberQ[derivedAxiomsFor[ru], axiom],
        "derived lemma"
    ,
    MemberQ[boundaryAxiomsFor[ru], axiom],
        "tape-model semantics"
    ,
    ! FreeQ[axiom, unbnd],
        "tape notation"
    ,
    FreeQ[axiom, Alternatives @@ $states],
        "run-length notation"
    ,
    True,
        "unjustified assumption"
]

proofRestsOnlyOnMachine[ru_] := AllTrue[cachedProofFor[ru]["Axioms"], proofInputRole[#, ru] =!= "unjustified assumption"&] && TrueQ[cachedProofFor[ru]["Valid"]]

(* === Proof graph === *)

normaliseLabel[lab_] := If[ListQ[lab] && Length[lab] == 2, {ToString[lab[[1]]], lab[[2]]}, lab]

$axiomBackground = $InductiveProofColors["AxiomBackground"]

$axiomTextColor = $InductiveProofColors["AxiomText"]

$theoremBackground = $InductiveProofColors["TheoremBackground"]

$theoremTextColor = $InductiveProofColors["TheoremText"]

$axiomFrameColor = $InductiveProofColors["AxiomFrame"]

$theoremFrameColor = $InductiveProofColors["TheoremFrame"]

$inductionFill = $InductiveProofColors["InductionFill"]

$inductionStroke = $InductiveProofColors["InductionStroke"]

$inductionVertexStyle = Directive[$inductionFill, EdgeForm[{$InductiveProofColors["InductionVertexEdge"], AbsoluteThickness[1.6]}]]

$eventCircleSize = 9

$vertexBoxRounding = 3

$boxPadding = {4, 4}; (* {horizontal, vertical} clear space inside a vertex label box *)

$proofLayoutScale = 0.55

(* === L2: shared vertex primitives (one place, identical output) === *)

$boxMargins = {4, 3}; $boxRounding = 3; $boxEdgeThickness = 0.5; $arrowGap = 0

(* arrow-tip gaps applied at render time (not baked into the cached layout): into a box
   (circle->box arrows) and into a circle (box->circle arrows), each defaulting to $arrowGap. *)

$boxArrowGap = 0; $circleArrowGap = 0

discVertex[fill_, stroke_, px_, thick_ : 0.8] := (
    Inset[
        Graphics[
            {fill, Disk[], stroke, AbsoluteThickness[thick], Circle[]}, ImageSize -> px, PlotRangePadding -> 0
        ]
        ,
        #1
    ]&
)

(* Pull a {fillColour, strokeColour} pair out of a vertex-style Directive (e.g. $axiomVertexStyle,
   eventVertexStyle[...]) so the cloud can be drawn with the SAME Inset disc as the proof while
   keeping the shared multiway colours. *)

styleFillStroke[dir_] := {
    FirstCase[dir, c : (_Hue | _RGBColor | _GrayLevel | _LightDarkSwitched) :> c, $InductiveProofColors["FallbackFrame"], Infinity]
    ,
    FirstCase[
        {FirstCase[dir, HoldPattern[EdgeForm[e_]] :> e, $InductiveProofColors["FallbackFrame"], Infinity]},
        c : (_Hue | _RGBColor | _GrayLevel | _LightDarkSwitched) :> c,
        $InductiveProofColors["FallbackFrame"],
        Infinity
    ]
}

(* A vertex box: Framed around the content. pad = {horizontal, vertical} margins. *)

boxGraphic[content_, bg_, edge_, rounding_, pad_, onAxis_ : False] := Framed[
    content,
    Background -> bg,
    RoundingRadius -> rounding,
    FrameStyle -> Directive[edge, AbsoluteThickness[$boxEdgeThickness]],
    FrameMargins -> {{pad[[1]], pad[[1]]}, {pad[[2]], pad[[2]]}}
]

styledBox[content_, bg_] := boxGraphic[content, bg, frameColorFor[bg], $boxRounding, $boxMargins]

inductionNodeShape = discVertex[$inductionFill, $inductionStroke, 1.5 $eventCircleSize, 1.6]

labelBox[content_, bg_, rounding_ : $vertexBoxRounding, frame_ : Automatic, onAxis_ : False] := With[{
    g = boxGraphic[
        Style[content, $InductiveProofColors["LabelText"]],
        bg,
        frame /. Automatic -> frameColorFor[bg],
        rounding,
        $boxPadding,
        onAxis
    ]
},
    (Inset[g, #1]&)
]

$axiomHue = $InductiveProofColors["AxiomHue"]

$axiomVertexEdge = $InductiveProofColors["AxiomVertexEdge"]

$theoremHue = $InductiveProofColors["TheoremHue"]

$axiomVertexStyle = Directive[Opacity[0.7], $axiomHue, EdgeForm[$axiomVertexEdge]]

$theoremVertexStyle = Directive[Opacity[0.7], $theoremHue, EdgeForm[$theoremFrameColor]]

$goalVertexStyle = $theoremVertexStyle

(* The one place a multiway state's vertex style is decided: axiom (generation-0) states green,
   everything else teal. Shared by MultiwayRuleGraph's ruleSpaceGraph and by the cloud in
   MultiwayInductiveProofPanel so the two render identically. Events keep eventVertexStyle. *)

multiwayStateStyle[isAxiom_] := If[TrueQ[isAxiom], $axiomVertexStyle, $theoremVertexStyle]

equationVertexShape[content_, isAx_, rounding_ : $vertexBoxRounding] := labelBox[
    content,
    If[isAx, $axiomBackground, $theoremBackground],
    rounding,
    Automatic,
    TrueQ[$centerOnEquals]
]

whiteVertexShape[content_] := labelBox[content, $cellBackground]

$defaultEventFill = $InductiveProofColors["DefaultEventFill"]

$defaultEventStroke = $InductiveProofColors["DefaultEventStroke"]

$criticalPairEventFill = $InductiveProofColors["CriticalPairEventFill"]

$criticalPairEventStroke = $InductiveProofColors["CriticalPairEventStroke"]

eventColorsFor[lab_] := If[ ! FreeQ[lab, "CriticalPairLemma" | CriticalPairLemma],
    {$criticalPairEventFill, $criticalPairEventStroke}
    ,
    {$defaultEventFill, $defaultEventStroke}
]

eventVertexShape[sz_ : 8, lab_ : None] := With[{ce = eventColorsFor[lab]},
    discVertex[ce[[1]], ce[[2]], sz]
]

eventVertexStyle[lab_ : None] := With[{ce = eventColorsFor[lab]},
    Directive[ce[[1]], EdgeForm[{ce[[2]], AbsoluteThickness[0.8]}]]
]

$equationalEdgeColor = $InductiveProofColors["EquationalEdge"]

$pathHighlight = $InductiveProofColors["PathHighlight"]

$pathHighlightBackground = $InductiveProofColors["PathHighlightBackground"]

$inductionEdgeColor = $inductionStroke

$inductionEdgeThickness = 2.4

$inductionEdgeThicknessCompact = 1.2

(* inductionThickness default is Automatic, resolved to $inductionEdgeThickness IN THE BODY: an
   optional-argument default `x_ : $global` is frozen at the global's value when the DownValue
   is set and does NOT track a later Block, so the InductionEdgeThickness option never reached
   the edge, so read the global in the body instead. *)

edgeStyleFor[tag_, inductionThickness_ : Automatic] := If[ MemberQ[{"Induction", "IndApp", "IndIn"}, ToString[tag]],
    Directive[
        $inductionEdgeColor,
        AbsoluteThickness[Replace[inductionThickness, Automatic :> $inductionEdgeThickness]]
    ]
    ,
    Directive[$equationalEdgeColor]
]

$inductionRuleBackground = $InductiveProofColors["InductionRuleBackground"]

$identityGlyph = TraditionalForm[t == t]

$qedSymbol = "■"

frameColorFor[c_] := switchedColor[
    Function[cc, Module[{h = ColorConvert[cc, Hue]}, Hue[h[[1]], Min[1, h[[2]] * 2.2 + 0.06], Max[0, h[[3]] * 0.8]]]]
    ,
    c
]

predicateAtIndex[ix_] := Subscript[P, ix]

$runLengthVariable = m

inductionHypothesisVertexShape[ihStmt_] := labelBox[
    renderGraphEquation[ihStmt],
    $inductionFill,
    $vertexBoxRounding,
    $InductiveProofColors["InductionVertexEdge"],
    TrueQ[$centerOnEquals]
]

$inductionHypothesisVertexStyle = $inductionVertexStyle

$inductionRuleCaption = With[{mIt = $runLengthVariable},
    Framed[
        Row[
            {
                predicateAtIndex[0],
                " ∧ (",
                predicateAtIndex[mIt],
                "  ",
                predicateAtIndex[Row[{mIt, "+1"}]],
                ")",
                "   ⟶   ",
                TraditionalForm[ForAll[mIt, predicateAtIndex[mIt]]]
            }
        ]
        ,
        Background -> $inductionRuleBackground
        ,
        FrameStyle -> Directive[frameColorFor[$inductionRuleBackground]]
        ,
        FrameMargins -> {{4, 4}, {2, 2}}
        ,
        RoundingRadius -> 3
    ]
]

inductionNodeQ[v_] := ListQ[v] && Length[v] == 2 && v[[2]] === "Induction"

goalNodeQ[v_] := ListQ[v] && Length[v] == 2 && v[[2]] === "Goal"

apparatusPrefixQ[p_] := StringQ[p] && (p === "Link" || StringEndsQ[p, ":Link"])

$rasterDimsCache = <||>

rasterDims[graphic_] := With[{k = Hash[graphic]},
    Lookup[
        $rasterDimsCache,
        k,
        $rasterDimsCache[k] = Quiet @ Check[ImageDimensions[Rasterize[graphic, ImageResolution -> 144]], {300., 58.}]
    ]
]

(* {width, height} in PRINTER'S POINTS, the same unit as ImageSize / FrameMargins / FontSize, so
   the layout, the box, and the cell size all live in one unit. *)

$boxBBoxCache = <||>

(* {width, height} of a box vertex, in points, so the layout can reserve room for it. Measure the
   actual rendered image: Rasterize "BoundingBox" reports the font line-box (with leading), ~6pt
   taller than a Framed box really draws, which left edges clipping above the visible border.
   ImageDimensions of the render is the true extent. *)

boxBBox[graphic_] := With[{k = Hash[graphic]},
    Lookup[
        $boxBBoxCache
        ,
        k
        ,
        $boxBBoxCache[k] = Quiet
        @
        Check[N[ImageDimensions[Rasterize[graphic, "Image", ImageResolution -> 144]] 72/144], {150., 20.}]
    ]
]

eventVertexQ[v_] := ListQ[v] && Length[v] == 2 &&
    (
        (ListQ[v[[2]]] && MemberQ[{"ChainEvent", "SubstEvent"}, v[[2, 1]]])
        ||
        (ListQ[v[[2]]] && Length[v[[2]]] == 2 && ToString[v[[2, 1]]] === "Event")
        ||
        v[[1]] === "MWEv"
        ||
        (
            ListQ[v[[2]]]
            &&
            Length[v[[2]]] >= 3
            &&
            ToString[v[[2, 1]]] === "Graft"
            &&
            ToString[v[[2, 3]]] === "Ev"
        )
    )

(* Axiom vertices = the proof's given equations: direct axiom copies {pfx,{"AxCopy",rank}} and the
   axiom applications inside a grafted lemma {pfx,{"Graft",ctr,"Ax",name}}. These are the
   logical sources of the proof – distinct from in-degree-0 statement/reflexivity vertices that
   are not axioms. *)

axiomVertexQ[v_] := ListQ[v] && Length[v] == 2 && ListQ[v[[2]]] &&
    (
        MatchQ[v[[2]], {"AxCopy", _}]
        ||
        (Length[v[[2]]] >= 3 && ToString[v[[2, 1]]] === "Graft" && ToString[v[[2, 3]]] === "Ax")
    )

(* An identity "theorem" introduced into a case is a reflexivity a==a: its held content releases to
   True (or to an Equal with identical sides). It is a given fed into an event just like an
   axiom, so AxiomRows / AxiomGap treat axiomLikeQ (axiom OR identity statement) uniformly. *)

identityStatementQ[v_] := ListQ[v] && Length[v] == 2 && MatchQ[v[[2]], _HoldForm] &&
    With[{eq = ReleaseHold[v[[2]]]},
        eq === True || (MatchQ[eq, _Equal] && eq[[1]] === eq[[2]])
    ]

axiomLikeQ[v_] := axiomVertexQ[v] || identityStatementQ[v]

graftStmtVertex[pfx_, ctr_, name_, contentH_] := With[{k = {pfx, {"Graft", ctr, "St", name}}},
    {k, k -> equationVertexShape[renderGraphEquation[contentH], False], k -> $theoremVertexStyle}
]

graftAxiomVertex[pfx_, ctr_, name_, rule_] := With[{k = {pfx, {"Graft", ctr, "Ax", name}}, eq = rule /. Verbatim[Pattern][s_, _] :> s},
    {
        k,
        k -> equationVertexShape[renderGraphEquation[HoldForm @@ {eq[[1]] == eq[[2]]}], True],
        k -> $axiomVertexStyle
    }
]

graftEventVertex[pfx_, ctr_, name_, lab_] := With[{k = {pfx, {"Graft", ctr, "Ev", name}}},
    {k, k -> eventVertexShape[$eventCircleSize, lab], k -> eventVertexStyle[lab]}
]

graftTargetChain[tgt_, ctr_, chain_] := Module[{pfx = tgt[[1]], refl, init},
    refl = graftStmtVertex[pfx, ctr, "Refl", Last[chain]["StmtH"]];
    init = <|
        "prev" -> refl[[1]],
        "verts" -> {refl[[1]]},
        "shapes" -> {refl[[2]]},
        "styles" -> {refl[[3]]},
        "edges" -> {}
    |>;
    KeyDrop[
        Fold[
            Function[{state, i},
                Module[{row = chain[[i]], ev, axRecords, outRecord, outKey, edgesAdd},
                    ev = graftEventVertex[pfx, ctr, i, ToString[row["Key"][[1]]]];
                    axRecords = Join[
                        If[ KeyExistsQ[row["Proof"], "Rule"],
                            {graftAxiomVertex[pfx, ctr, {i, 1}, row["Proof"]["Rule"]]}
                            ,
                            {}
                        ]
                        ,
                        If[ KeyExistsQ[row["Proof"], "MatchingRule"],
                            {graftAxiomVertex[pfx, ctr, {i, 2}, row["Proof"]["MatchingRule"]]}
                            ,
                            {}
                        ]
                    ];
                    outRecord = If[i == 1, None, graftStmtVertex[pfx, ctr, i - 1, chain[[i - 1]]["StmtH"]]];
                    outKey = If[i == 1, tgt, outRecord[[1]]];
                    edgesAdd = Join[
                        {DirectedEdge[state["prev"], ev[[1]]]},
                        Map[DirectedEdge[#[[1]], ev[[1]]]&, axRecords],
                        {DirectedEdge[ev[[1]], outKey]}
                    ];
                    <|
                        "prev" -> outKey
                        ,
                        "verts" -> Join[state["verts"], {ev[[1]]}, Map[#[[1]]&, axRecords], If[outRecord === None, {}, {outRecord[[1]]}]]
                        ,
                        "shapes" -> Join[state["shapes"], {ev[[2]]}, Map[#[[2]]&, axRecords], If[outRecord === None, {}, {outRecord[[2]]}]]
                        ,
                        "styles" -> Join[state["styles"], {ev[[3]]}, Map[#[[3]]&, axRecords], If[outRecord === None, {}, {outRecord[[3]]}]]
                        ,
                        "edges" -> Join[state["edges"], edgesAdd]
                    |>
                ]
            ]
            ,
            init
            ,
            Range[Length[chain], 1, -1]
        ]
        ,
        "prev"
    ]
]

graftLemma[g_Graph, lemmaProof_ProofObject, mergeAsAxiom_ : False] := Module[{
    verts = VertexList[g],
    edges = EdgeList[g],
    sf,
    st,
    es,
    ds,
    keys,
    rows,
    thm,
    sOf,
    targets,
    chain,
    grafts,
    newV,
    newSF,
    newST,
    newE,
    finalSF,
    finalST
},
    sf = graphOption[g, VertexShapeFunction];
    st = graphOption[g, VertexStyle];
    es = graphOption[g, EdgeStyle];
    ds = lemmaProof["ProofDataset"];
    keys = Normal[Keys[ds]];
    rows = Table[
        <|
            "Key" -> keys[[i]]
            ,
            "StmtH" -> Normal[ds[i]]["Statement"]
            ,
            "Proof" -> With[{pr = Normal[ds[i]]["Proof"]},
                If[AssociationQ[pr], pr, <||>]
            ]
        |>
        ,
        {i, Length[keys]}
    ];
    thm = SelectFirst[rows, #Key[[1]] === "Hypothesis"&]["StmtH"] //. HoldForm[zz_] :> zz;
    sOf[v_] := Which[ 
        MatchQ[v, {_, _HoldForm}],
            ReleaseHold[Replace[v[[2]], HoldForm[Tooltip[ss_, _]] :> HoldForm[ss]]]
        ,
        MatchQ[v, {_, {"ChainAxiom", _, _HoldForm}}],
            ReleaseHold[Replace[v[[2, 3]], HoldForm[Tooltip[ss_, _]] :> HoldForm[ss]]]
        ,
        True,
            None
    ];
    targets = Select[
        verts
        ,
        With[{s2 = sOf[#]},
            s2 =!= None && MatchQ[s2, _Equal] &&
                (
                    canonicalizeVariables[s2] === canonicalizeVariables[thm]
                    ||
                    canonicalizeVariables[s2] === canonicalizeVariables[thm[[2]] == thm[[1]]]
                )
        ]&
    ];
    If[targets === {}, Return[g]];
    chain = Select[rows, MemberQ[{"SubstitutionLemma", "CriticalPairLemma", "Conclusion"}, #Key[[1]]]&];
    If[chain === {}, Return[g]];
    grafts = MapIndexed[graftTargetChain[#1, First[#2], chain]&, targets];
    newV = Flatten[Map[#["verts"]&, grafts], 1];
    newSF = Flatten[Map[#["shapes"]&, grafts], 1];
    newST = Flatten[Map[#["styles"]&, grafts], 1];
    newE = Flatten[Map[#["edges"]&, grafts], 1];
    finalSF = Fold[
        Function[{shapes, tgt},
            Map[
                If[ #[[1]] === tgt,
                    tgt -> equationVertexShape[renderGraphEquation[HoldForm @@ {sOf[tgt]}], mergeAsAxiom]
                    ,
                    #
                ]&
                ,
                shapes
            ]
        ]
        ,
        sf
        ,
        targets
    ];
    finalST = Fold[
        Function[{styles, tgt},
            Map[If[#[[1]] === tgt, tgt -> If[mergeAsAxiom, $axiomVertexStyle, $theoremVertexStyle], #]&, styles]
        ]
        ,
        st
        ,
        targets
    ];
    Graph[
        Join[verts, newV],
        Join[edges, newE],
        VertexShapeFunction -> Join[finalSF, newSF],
        VertexStyle -> Join[finalST, newST],
        noVertexLabels[Join[verts, newV]],
        EdgeStyle -> Join[es, Map[# -> Directive[$equationalEdgeColor]&, newE]],
        PerformanceGoal -> "Quality"
    ]
]

lemmaComponentOf[v_] := If[ ListQ[v] && Length[v] >= 1 && StringQ[v[[1]]],
    Switch[ v[[1]],
        "Base",
            "Base"
        ,
        "Step",
            "Step"
        ,
        "Link",
            "Apparatus"
        ,
        _,
            "Other"
    ]
    ,
    "Other"
]

namespaceVertex[name_, v_] := If[ListQ[v] && Length[v] >= 1, ReplacePart[v, 1 -> name <> ":" <> ToString[v[[1]]]], v]

graftInductiveLemma[
    g_Graph,
    name_String,
    lemmaProof_Association,
    hostRecords_Association,
    mergeAsAxiom_ : False,
    components_ : All
] := Module[{
    copyAxioms = hostRecords["copyAxioms"],
    copyDisplays = hostRecords["copyDisplays"],
    lr,
    goalBody,
    targets,
    fused,
    cls,
    dispOf,
    rebuilt,
    keep,
    ns,
    nsOf,
    lemEdges,
    lemSF,
    lemST,
    addedVerts,
    allVerts,
    hostSF,
    hostST,
    instEdges
},
    lr = fepProofRecords[lemmaProof];
    If[! AssociationQ[lr], Return[g]];
    goalBody = forAllBody[lemmaProof["Goal"]];
    targets = Select[
        Keys[
            Select[
                copyAxioms
                ,
                canonicalizeVariables[#[[2]]] === canonicalizeVariables[goalBody]
                ||
                canonicalizeVariables[#[[2]]] === canonicalizeVariables[goalBody[[2]] == goalBody[[1]]]&
            ]
        ]
        ,
        MemberQ[VertexList[g], #]&
    ];
    If[targets === {}, Return[g]];
    fused = First[targets];
    cls = If[mergeAsAxiom, "axiom", "derived"];
    dispOf[t_] := With[{r = SelectFirst[copyDisplays, #[[1]] === t&, None]},
        If[r === None, goalBody, r[[2]]]
    ];
    rebuilt[t_] := fepStmtRecord[t, dispOf[t], cls, {0, 0}, 0];
    keep = Select[lr["verts"], # === lr["goalV"] || components === All || MemberQ[components, lemmaComponentOf[#]]&];
    ns[v_] := namespaceVertex[name, v];
    nsOf = Association[Map[# -> ns[#]&, keep]];
    nsOf[lr["goalV"]] = fused;
    lemEdges = Select[lr["edges"], MemberQ[keep, #[[1]]] && MemberQ[keep, #[[2]]]&];
    lemSF = Select[lr["shapes"], MemberQ[keep, #[[1]]] && #[[1]] =!= lr["goalV"]&];
    lemST = Select[lr["styles"], MemberQ[keep, #[[1]]] && #[[1]] =!= lr["goalV"]&];
    addedVerts = DeleteCases[Map[nsOf, keep], fused];
    allVerts = Join[VertexList[g], addedVerts];
    hostSF = Fold[
        Function[{sf, t},
            Map[If[#[[1]] === t, rebuilt[t]["shape"], #]&, sf]
        ]
        ,
        graphOption[g, VertexShapeFunction]
        ,
        targets
    ];
    hostST = Fold[
        Function[{st, t},
            Map[If[#[[1]] === t, rebuilt[t]["style"], #]&, st]
        ]
        ,
        graphOption[g, VertexStyle]
        ,
        targets
    ];
    instEdges = Map[DirectedEdge[fused, #, "Instantiate"]&, Rest[targets]];
    Graph[
        allVerts
        ,
        Join[EdgeList[g], Map[# /. Normal[nsOf]&, lemEdges], instEdges]
        ,
        VertexShapeFunction -> Join[hostSF, Map[(nsOf[#[[1]]] -> #[[2]])&, lemSF]]
        ,
        VertexStyle -> Join[hostST, Map[(nsOf[#[[1]]] -> #[[2]])&, lemST]]
        ,
        noVertexLabels[allVerts]
        ,
        EdgeStyle -> Join[
                graphOption[g, EdgeStyle],
                Map[(# /. Normal[nsOf]) -> edgeStyleFor[edgeTag[#]]&, lemEdges],
                Map[# -> Directive[$equationalEdgeColor]&, instEdges]
            ]
        ,
        PerformanceGoal -> "Quality"
    ]
]

(* === Token-event proof graphs === *)

$rtepg = ResourceFunction[
    ResourceObject[<|
        "Name" -> "ReverseTokenEventProofGraph",
        "UUID" -> "3b469989-6d05-48b2-ba5a-fd8b427c757c",
        "ResourceType" -> "Function",
        "ResourceLocations" -> {
            CloudObject["https://www.wolframcloud.com/obj/wolframphysics/Resources/3b4/3b469989-6d05-48b2-ba5a-fd8b427c757c"]
        },
        "FunctionLocation" -> CloudObject["https://www.wolframcloud.com/obj/wolframphysics/Resources/3b4/3b469989-6d05-48b2-ba5a-fd8b427c757c/download/DefinitionData"],
        "ShortName" -> "ReverseTokenEventProofGraph",
        "SymbolName" -> "FunctionRepository`$3b4699896d0548b2ba5afd8b427c757c`ReverseTokenEventProofGraph"
    |>]
]

revCaseDropVertices[v_, edges_, axStmts_, trueQ_, instQ_] := If[ ! MatchQ[v, {"Event", _}],
    {}
    ,
    Module[{ins, outs, realIns, seedFree},
        ins = DeleteDuplicates[Cases[edges, DirectedEdge[s_, t_, ___] /; t === v :> s]];
        outs = DeleteDuplicates[Cases[edges, DirectedEdge[x_, t_, ___] /; x === v :> t]];
        realIns = Select[ins, ! trueQ[#]&];
        seedFree[p_] := DeleteDuplicates[Cases[edges, DirectedEdge[x_, t_, ___] /; x === p :> t]] === {v}
        &&
        Cases[edges, DirectedEdge[s_, x_, ___] /; x === p :> s] === {};
        Which[ 
            Length[ins] < 2,
                Join[{v}, Select[ins, seedFree]]
            ,
            Length[realIns] == 1
                &&
                Length[ins] == 2
                &&
                Length[outs] == 1
                &&
                MemberQ[axStmts, ReleaseHold[realIns[[1]]]]
                &&
                instQ[outs[[1]], realIns[[1]]],
                Join[{v}, Select[ins, trueQ[#] && seedFree[#]&]]
            ,
            True,
                {}
        ]
    ]
]

revCaseRename[v_, keepE_] := If[ ! (MatchQ[v, _HoldForm] && ReleaseHold[v] === True),
    Nothing
    ,
    Module[{ev, out},
        ev = FirstCase[keepE, DirectedEdge[s_, t_, ___] /; s === v :> t, None];
        out = If[ev === None, None, FirstCase[keepE, DirectedEdge[xx_, t_, ___] /; xx === ev :> t, None]];
        If[ out =!= None && MatchQ[out, _HoldForm] && MatchQ[ReleaseHold[out], _Equal],
            With[{rr = ReleaseHold[out][[2]]},
                v -> HoldForm[rr == rr]
            ]
            ,
            Nothing
        ]
    ]
]

revCase[pobj_ProofObject, goalStmt_] := Module[{g, edges, dropV, keepV, keepE, ren},
    g = VertexReplace[pobj["TokenEventProofGraph", "TokenLabeling" -> True], HoldForm[Tooltip[st_, _]] :> HoldForm[st]];
    g = $rtepg[g, HoldForm @@ {goalStmt}];
    If[! MatchQ[g, _Graph], Return[g]];
    edges = EdgeList[g];
    dropV = Module[{trueQ, instQ, axStmts, ds = pobj["ProofDataset"], keys},
        keys = Normal[Keys[ds]];
        axStmts = Table[
            If[MatchQ[keys[[i]], {"Axiom", _}], ReleaseHold[Normal[ds[i]]["Statement"]], Nothing],
            {i, Length[keys]}
        ];
        trueQ[u_] := MatchQ[u, _HoldForm] && ReleaseHold[u] === True;
        instQ[o_, p_] := MatchQ[o, _HoldForm]
        &&
        MatchQ[p, _HoldForm]
        &&
        Module[{pp = ReleaseHold[p], oo, vars, pat},
            If[ ! MatchQ[pp, _Equal],
                False
                ,
                oo = ReleaseHold[o];
                vars = DeleteDuplicates[Cases[pp, s_Symbol /; MemberQ[$formalVariables, s], {0, Infinity}]];
                pat = pp /. Thread[vars -> (Pattern[#, _]& /@ vars)];
                MatchQ[oo, pat] || MatchQ[oo, pat[[2]] == pat[[1]]]
            ]
        ];
        Flatten[Map[revCaseDropVertices[#, edges, axStmts, trueQ, instQ]&, VertexList[g]], 1]
    ];
    keepV = DeleteCases[VertexList[g], Alternatives @@ dropV];
    keepE = Select[edges, ! MemberQ[dropV, #[[1]]] && ! MemberQ[dropV, #[[2]]]&];
    ren = DeleteCases[Map[revCaseRename[#, keepE]&, keepV], Nothing];
    Graph[keepV /. ren, keepE /. ren]
]

revBox[content_, fc_ : Automatic, bg_ : $cellBackground, frame_ : Automatic] := labelBox[content, bg]

proofDatasetInfo[pobj_, ourAx_] := Module[{ds = pobj["ProofDataset"], keys, statements, axiomStatements, flips, bare},
    bare = ourAx /. ForAll[_, b_] :> b;
    keys = Normal[Keys[ds]];
    statements = Association[Table[keys[[i]] -> ReleaseHold[Normal[ds[i]]["Statement"]], {i, Length[keys]}]];
    axiomStatements = Map[statements[#]&, Select[keys, MatchQ[#, {"Axiom", _}]&]];
    flips = Select[
        axiomStatements
        ,
        Function[st,
            MatchQ[st, _Equal]
            &&
            ! AnyTrue[bare, canonicalizeVariables[st] === canonicalizeVariables[#]&]
            &&
            AnyTrue[bare, MatchQ[#, _Equal] && canonicalizeVariables[st] === canonicalizeVariables[#[[2]] == #[[1]]]&]
        ]
    ];
    <|
        "Ax" -> axiomStatements
        ,
        "Flips" -> DeleteDuplicates[flips]
        ,
        "AxPat" -> Map[
            Function[st,
                Module[
                    {vars = DeleteDuplicates[Cases[st, s_Symbol /; MemberQ[$formalVariables, s], {0, Infinity}]]},
                    st /. Thread[vars -> (Pattern[#, _]& /@ vars)]
                ]
            ]
            ,
            axiomStatements
        ]
    |>
]

criticalPairUse[ruleStmt_, ev_, edges_] := If[ ! MatchQ[ruleStmt, _Equal],
    0
    ,
    Module[{l, r, others, out},
        {l, r} = List @@ ruleStmt;
        others = Cases[
            edges
            ,
            DirectedEdge[s_, t_, ___] /; t === ev && MatchQ[s, _HoldForm] && ReleaseHold[s] =!= ruleStmt
            :>
            ReleaseHold[s]
        ];
        out = Cases[edges, DirectedEdge[xx_, t_, ___] /; xx === ev :> ReleaseHold[t]];
        If[Length[others] != 1 || Length[out] != 1, Return[0]];
        FirstCase[
            Flatten[
                Map[
                    Function[pr,
                        Module[{pp = pr[[1]], qq = pr[[2]], pvars, pat},
                            pvars = DeleteDuplicates[Cases[pp, s_Symbol /; MemberQ[$formalVariables, s], {0, Infinity}]];
                            pat = pp /. Thread[pvars -> (Pattern[#, _]& /@ pvars)];
                            Map[
                                Function[pos,
                                    If[ If[ pos === {},
                                        Replace[others[[1]], RuleDelayed @@ {pat, qq}]
                                        ,
                                        ReplacePart[others[[1]], pos -> Replace[Extract[others[[1]], pos], RuleDelayed @@ {pat, qq}]]
                                    ]
                                    ===
                                    out[[1]],
                                        {Extract[others[[1]], pos], Extract[out[[1]], pos]}
                                        ,
                                        Nothing
                                    ]
                                ]
                                ,
                                Position[others[[1]], _ ? (MatchQ[#, pat]&), {0, Infinity}, Heads -> False]
                            ]
                        ]
                    ]
                    ,
                    {{l, r}, {r, l}}
                ]
                ,
                1
            ]
            ,
            _
            ,
            0
            ,
            {1}
        ]
    ]
]

fepStmtRecord[k_, dispStmt_, cls_, pos_, xoff_] := <|
    "v" -> k
    ,
    "coord" -> pos + {xoff, 0}
    ,
    "shape" -> (k -> revBox[
        renderGraphEquation[If[MatchQ[dispStmt, _HoldForm], dispStmt, HoldForm @@ {dispStmt}]]
        ,
        If[cls === "derived", $theoremTextColor, $axiomTextColor]
        ,
        Switch[ cls,
            "goal",
                $theoremBackground
            ,
            "axiom",
                $axiomBackground
            ,
            _,
                $theoremBackground
        ]
        ,
        Switch[ cls,
            "goal",
                $theoremFrameColor
            ,
            "axiom",
                $axiomFrameColor
            ,
            _,
                $theoremFrameColor
        ]
    ])
    ,
    "style" -> (k -> Switch[ cls,
        "goal",
            Directive[Opacity[0.7], $theoremHue, EdgeForm[$theoremFrameColor]]
        ,
        "axiom",
            Directive[Opacity[0.7], $InductiveProofColors["TokenEventAxiomHue"], EdgeForm[$axiomFrameColor]]
        ,
        _,
            Directive[Opacity[0.7], EdgeForm[$theoremFrameColor], $theoremHue]
    ])
|>

fepEventRecord[k_, lab_, pos_, xoff_] := <|
    "v" -> k,
    "coord" -> pos + {xoff, 0},
    "shape" -> k -> eventVertexShape[$eventCircleSize, lab],
    "style" -> k -> eventVertexStyle[lab]
|>

fepCaseVertices[g_, prefix_, pobj_, goalStmt_, xoff_, data_] := Module[{
    vs = VertexList[g],
    emb = GraphEmbedding[g],
    edges = EdgeList[g],
    info,
    axQ,
    ihStmtQ,
    posOfLocal,
    copyEdgeQ,
    copyRank,
    edgeResults,
    copyDefs,
    copyAxioms,
    copyDisplays,
    newEdges,
    mainRecords,
    copyRecords,
    allRecords
},
    info = proofDatasetInfo[pobj, Join[data["Axioms"], {data["IH"]}]];
    axQ[v_] := MatchQ[v, _HoldForm] && MemberQ[info["Ax"], ReleaseHold[v]];
    ihStmtQ[v_] := MatchQ[v, _HoldForm] &&
        With[{st = ReleaseHold[v]},
            st === data["IH"] || st === (data["IH"][[2]] == data["IH"][[1]])
        ];
    posOfLocal[v_] := emb[[First[FirstPosition[vs, v]]]];
    copyEdgeQ[e_] := With[{parts = List @@ e},
        axQ[parts[[1]]]
        &&
        ! ihStmtQ[parts[[1]]]
        &&
        ListQ[parts[[2]]]
        &&
        ToString[parts[[2]][[1]]] === "Event"
    ];
    copyRank = AssociationThread[Select[Range[Length[edges]], copyEdgeQ[edges[[#]]]&] -> Range[Count[edges, _ ? copyEdgeQ]]];
    edgeResults = MapIndexed[
        Function[{e, idx},
            With[{j = First[idx], parts = List @@ e},
                If[ copyEdgeQ[e],
                    With[{cName = {"AxCopy", copyRank[j]}, st = ReleaseHold[parts[[1]]], t = parts[[2]]},
                        With[{ui = criticalPairUse[st, t, edges]},
                            With[{
                                disp = Which[ 
                                    ListQ[ui],
                                        ui[[1]] == ui[[2]]
                                    ,
                                    MemberQ[info["Flips"], st] && MatchQ[st, _Equal],
                                        st[[2]] == st[[1]]
                                    ,
                                    True,
                                        st
                                ]
                            },
                                <|
                                    "copyDef" -> cName -> {disp, posOfLocal[t] + {-2, 1.5}},
                                    "copyAx" -> {prefix, cName} -> st,
                                    "edge" -> DirectedEdge @@ Join[{{prefix, cName}, {prefix, t}}, Drop[parts, 2]]
                                |>
                            ]
                        ]
                    ]
                    ,
                    <|
                        "copyDef" -> Nothing,
                        "copyAx" -> Nothing,
                        "edge" -> DirectedEdge @@ Join[{{prefix, parts[[1]]}, {prefix, parts[[2]]}}, Drop[parts, 2]]
                    |>
                ]
            ]
        ]
        ,
        edges
    ];
    copyDefs = DeleteCases[Map[#["copyDef"]&, edgeResults], Nothing];
    copyAxioms = DeleteCases[Map[#["copyAx"]&, edgeResults], Nothing];
    copyDisplays = Map[({prefix, #[[1]]} -> #[[2, 1]])&, copyDefs];
    newEdges = Map[#["edge"]&, edgeResults];
    mainRecords = DeleteCases[
        Map[
            Function[i,
                Module[{v = vs[[i]], st, disp, cls},
                    Which[ 
                        ListQ[v] && Length[v] == 2 && ToString[v[[1]]] === "Event",
                            fepEventRecord[{prefix, v}, v[[2, 1]], emb[[i]], xoff]
                        ,
                        axQ[v] && ! ihStmtQ[v],
                            Nothing
                        ,
                        True,
                            st = ReleaseHold[v];
                            disp = Which[ 
                                st === True,
                                    v
                                ,
                                MemberQ[info["Flips"], st] && MatchQ[st, _Equal],
                                    st[[2]] == st[[1]]
                                ,
                                True,
                                    st
                            ];
                            cls = Which[ 
                                st === goalStmt,
                                    "goal"
                                ,
                                MemberQ[info["Ax"], st] || AnyTrue[info["AxPat"], MatchQ[st, #] || MatchQ[st, #[[2]] == #[[1]]]&],
                                    "axiom"
                                ,
                                True,
                                    "derived"
                            ];
                            fepStmtRecord[{prefix, v}, disp, cls, emb[[i]], xoff]
                    ]
                ]
            ]
            ,
            Range[Length[vs]]
        ]
        ,
        Nothing
    ];
    copyRecords = Map[
        Function[cd,
            fepStmtRecord[{prefix, cd[[1]]}, cd[[2, 1]], "axiom", cd[[2, 2]], xoff]
        ]
        ,
        copyDefs
    ];
    allRecords = Join[mainRecords, copyRecords];
    <|
        "verts" -> Map[#["v"]&, allRecords],
        "coords" -> Map[#["coord"]&, allRecords],
        "shapes" -> Map[#["shape"]&, allRecords],
        "styles" -> Map[#["style"]&, allRecords],
        "edges" -> newEdges,
        "copyAxioms" -> copyAxioms,
        "copyDisplays" -> copyDisplays
    |>
]

attachInductionApparatus[verts_, coords_, baseThmV_, stepThmV_, ihV_, data_] := Module[{posOf, mid, inductionNode = {"Link", "Induction"}, goalNode = {"Link", "Goal"}},
    posOf[v_] := coords[[First[FirstPosition[verts, v]]]];
    mid = (posOf[baseThmV] + posOf[stepThmV]) / 2;
    <|
        "verts" -> {inductionNode, goalNode}
        ,
        "coords" -> {mid + {0, -6}, mid + {0, -11}}
        ,
        "shapes" -> {
                inductionNode -> inductionNodeShape,
                goalNode -> labelBox[renderGraphUniversalGoal[m, data["IH"] /. n -> m], $theoremBackground]
            }
        ,
        "styles" -> {inductionNode -> $inductionVertexStyle, goalNode -> $goalVertexStyle}
        ,
        "edges" -> Join[
            {DirectedEdge[baseThmV, inductionNode, "IndIn"], DirectedEdge[stepThmV, inductionNode, "IndIn"]},
            If[ihV === None, {}, {DirectedEdge[ihV, inductionNode, "IndIn"]}],
            {DirectedEdge[inductionNode, goalNode, "IndIn"]}
        ]
    |>
]

fepProofRecords[data_Association] := Module[{
    bg,
    sg,
    stepXoff,
    baseRecords,
    stepRecords,
    verts,
    coords,
    shapes,
    styles,
    edges,
    baseThmV,
    stepThmV,
    ihV,
    hasApparatus
},
    bg = revCase[data["BaseProof"], data["BaseGoal"]];
    sg = revCase[data["StepProof"], data["StepGoal"]];
    If[! MatchQ[bg, _Graph] || ! MatchQ[sg, _Graph], Return[$Failed]];
    stepXoff = Max[GraphEmbedding[bg][[All, 1]]] - Min[GraphEmbedding[sg][[All, 1]]] + 15;
    baseRecords = fepCaseVertices[bg, "Base", data["BaseProof"], data["BaseGoal"], 0, data];
    stepRecords = fepCaseVertices[sg, "Step", data["StepProof"], data["StepGoal"], stepXoff, data];
    verts = Join[baseRecords["verts"], stepRecords["verts"]];
    coords = Join[baseRecords["coords"], stepRecords["coords"]];
    shapes = Join[baseRecords["shapes"], stepRecords["shapes"]];
    styles = Join[baseRecords["styles"], stepRecords["styles"]];
    edges = Join[baseRecords["edges"], stepRecords["edges"]];
    baseThmV = {"Base", HoldForm @@ {data["BaseGoal"]}};
    stepThmV = {"Step", HoldForm @@ {data["StepGoal"]}};
    ihV = SelectFirst[
        verts
        ,
        MatchQ[#, {"Step", _}] && MatchQ[#[[2]], _HoldForm] &&
            With[{st = ReleaseHold[#[[2]]]},
                st === data["IH"] || st === (data["IH"][[2]] == data["IH"][[1]])
            ]&
        ,
        None
    ];
    shapes = Map[If[#[[1]] === ihV, ihV -> inductionHypothesisVertexShape[data["IH"]], #]&, shapes];
    styles = Map[If[#[[1]] === ihV, ihV -> $inductionHypothesisVertexStyle, #]&, styles];
    hasApparatus = MemberQ[verts, baseThmV] && MemberQ[verts, stepThmV];
    If[ hasApparatus,
        With[{apparatus = attachInductionApparatus[verts, coords, baseThmV, stepThmV, ihV, data]},
            verts = Join[verts, apparatus["verts"]];
            coords = Join[coords, apparatus["coords"]];
            shapes = Join[shapes, apparatus["shapes"]];
            styles = Join[styles, apparatus["styles"]];
            edges = Join[edges, apparatus["edges"]]
        ]
    ];
    <|
        "verts" -> verts,
        "edges" -> edges,
        "coords" -> coords,
        "shapes" -> shapes,
        "styles" -> styles,
        "copyAxioms" -> Join[baseRecords["copyAxioms"], stepRecords["copyAxioms"]],
        "copyDisplays" -> Join[baseRecords["copyDisplays"], stepRecords["copyDisplays"]],
        "baseThmV" -> baseThmV,
        "stepThmV" -> stepThmV,
        "ihV" -> ihV,
        "goalV" -> If[hasApparatus, {"Link", "Goal"}, stepThmV]
    |>
]

fepGraphFromRecords[r_Association] := Graph[
    r["verts"]
    ,
    r["edges"]
    ,
    VertexCoordinates -> r["coords"]
    ,
    VertexShapeFunction -> r["shapes"]
    ,
    VertexStyle -> r["styles"]
    ,
    noVertexLabels[r["verts"]]
    ,
    EdgeStyle -> Map[
            Function[e,
                e -> edgeStyleFor[edgeTag[e]]
            ]
            ,
            r["edges"]
        ]
    ,
    PerformanceGoal -> "Quality"
    ,
    ImageSize -> Large
]

fepCombinedGraph[data_Association] := With[{r = fepProofRecords[data]},
    If[AssociationQ[r], fepGraphFromRecords[r], $Failed]
]

(* === Multiway rewriting === *)

runUnfoldWeight[e_] := LeafCount[e] + 4 * Count[e, succ, {0, Infinity}, Heads -> True]

orientByWeight[{lhs_, rhs_}, weight_] := If[weight[rhs] > weight[lhs], {rhs, lhs}, {lhs, rhs}]

axiomToOrientedRules[ax_, wfn_ : LeafCount] := Module[{vars = forAllVariables[ax], eq = forAllBody[ax], pattRules, l, r},
    If[! MatchQ[eq, _Equal], Return[{}]];
    pattRules = Map[# -> Pattern[Evaluate[#], _]&, vars];
    {l, r} = orientByWeight[{eq[[1]], eq[[2]]}, wfn];
    With[{lp = l /. pattRules, rr = r},
        If[MatchQ[lp, _Pattern], {}, {lp :> rr}]
    ]
]

axiomToMultiwayRules[ax_] := Module[{vars = forAllVariables[ax], eq = forAllBody[ax], pattRules},
    If[! MatchQ[eq, _Equal], Return[{}]];
    pattRules = Map[# -> Pattern[Evaluate[#], _]&, vars];
    With[{lhsP = eq[[1]] /. pattRules, rhsP = eq[[2]] /. pattRules, lhs = eq[[1]], rhs = eq[[2]]},
        Select[{lhsP :> rhs, rhsP :> lhs}, ! MatchQ[#[[1]], _Pattern]&]
    ]
]

multiwayStep[exprs_List, rules_List] := Module[{edges},
    edges = DeleteDuplicates[
        Flatten[
            Table[
                With[{positions = Prepend[Position[expr, _, {1, Infinity}, Heads -> False], {}]},
                    Table[
                        With[{
                            rewritten = If[pos === {}, Replace[expr, rule], ReplacePart[expr, pos -> Replace[Extract[expr, pos], rule]]]
                        },
                            If[rewritten =!= expr, DirectedEdge[expr, rewritten], Nothing]
                        ]
                        ,
                        {pos, positions}
                    ]
                ]
                ,
                {expr, exprs}
                ,
                {rule, rules}
            ]
        ]
    ];
    {DeleteDuplicates[Cases[edges, DirectedEdge[_, t_] :> t]], edges}
]

criticalPairAt[inner1_, inner2_, vars_, origVars_] := If[ MatchQ[inner1, Alternatives @@ vars] || MatchQ[inner2, Alternatives @@ vars],
    Nothing
    ,
    Module[{inductionVars, pattVars, sub},
        inductionVars = DeleteDuplicates[
            Join[
                Cases[{inner1, inner2}, (ones | zeros)[v_, __] /; MemberQ[vars, v] :> v, Infinity],
                Cases[{inner1, inner2}, succ[v_] /; MemberQ[vars, v] :> v, Infinity]
            ]
        ];
        pattVars = Complement[vars, inductionVars];
        sub = Thread[inductionVars -> Pick[origVars, MemberQ[inductionVars, #]& /@ vars]];
        {inner1 /. sub, inner2 /. sub, pattVars}
    ]
]

criticalPairsFromAxiom[eq_, vars_, origVars_] := If[ ! MatchQ[eq, _Equal],
    {}
    ,
    With[{lhs = eq[[1]], rhs = eq[[2]]},
        If[ ! (Head[lhs] === Head[rhs] && Length[lhs] === Length[rhs]),
            {}
            ,
            DeleteCases[
                Table[
                    If[ lhs[[k]] =!= rhs[[k]] && Delete[lhs, k] === Delete[rhs, k],
                        criticalPairAt[lhs[[k]], rhs[[k]], vars, origVars]
                        ,
                        Nothing
                    ]
                    ,
                    {k, Length[lhs]}
                ]
                ,
                Nothing
            ]
        ]
    ]
]

generateCriticalPairs[axioms_List] := Module[{stripped, varSets, origVarSets, newRules},
    {stripped, varSets, origVarSets} = Transpose[
        Table[
            Module[{vars = forAllVariables[ax], eq = forAllBody[ax], freshVars},
                freshVars = Table[Unique["v"], Length[vars]];
                eq = eq /. Thread[vars -> freshVars];
                {eq, freshVars, vars}
            ]
            ,
            {ax, axioms}
        ]
    ];
    newRules = DeleteDuplicatesBy[
        Flatten[
            Table[criticalPairsFromAxiom[stripped[[i]], varSets[[i]], origVarSets[[i]]], {i, Length[stripped]}],
            1
        ]
        ,
        Most
    ];
    Flatten[
        Table[
            Module[{l = cp[[1]], r = cp[[2]], vars = cp[[3]], allVars, pattRules, lP, rP},
                allVars = DeleteDuplicates[Cases[{l, r}, Alternatives @@ vars, Infinity]];
                pattRules = Map[# -> Pattern[Evaluate[#], _]&, allVars];
                lP = l /. pattRules;
                rP = r /. pattRules;
                Select[
                    {
                        Hold[RuleDelayed][lP, r] /. Hold[RuleDelayed] -> RuleDelayed,
                        Hold[RuleDelayed][rP, l] /. Hold[RuleDelayed] -> RuleDelayed
                    }
                    ,
                    ! MatchQ[#[[1]], _Pattern]&
                ]
            ]
            ,
            {cp, newRules}
        ]
    ]
]

derivedLemmaAxioms[pobj_ProofObject] := Module[{ds = pobj["ProofDataset"], keys},
    keys = Normal[Keys[ds]];
    Table[
        If[ MatchQ[keys[[i]], {"CriticalPairLemma" | "SubstitutionLemma", _}],
            Module[{st = ReleaseHold[Normal[ds[i]]["Statement"]], vars},
                vars = DeleteDuplicates[Cases[st, s_Symbol /; MemberQ[$formalVariables, s], {0, Infinity}]];
                If[vars === {}, st, ForAll[vars, st]]
            ]
            ,
            Nothing
        ]
        ,
        {i, Length[keys]}
    ]
]

renderMultiwayExpression[t_] := Which[ 
    t === True,
        $identityGlyph
    ,
    MatchQ[t, _Equal],
        renderGraphEquation[HoldForm @@ {t}]
    ,
    True,
        RenderConfiguration[t]
]

equationalProofPath[vertices_, allEdges_, initExprs_] := Module[{meetPoints = {}, proofPath = {}, proofEdges = {}, reachableFrom},
    If[ Length[initExprs] >= 2 && Length[allEdges] > 0,
        Module[{undirected = Graph[vertices, allEdges /. DirectedEdge -> UndirectedEdge]},
            reachableFrom[start_] := Module[{component},
                component = If[ MemberQ[vertices, start],
                    ConnectedComponents[undirected] // SelectFirst[MemberQ[#, start]&]
                    ,
                    {start}
                ];
                If[component === Missing["NotFound"], {start}, component]
            ];
            meetPoints = Complement[Intersection[reachableFrom[initExprs[[1]]], reachableFrom[initExprs[[2]]]], initExprs];
            If[ Length[meetPoints] > 0,
                Module[{directed = Graph[vertices, allEdges], best, path1, path2},
                    best = First[
                        SortBy[
                            meetPoints,
                            GraphDistance[directed, initExprs[[1]], #] + GraphDistance[directed, initExprs[[2]], #]&
                        ]
                    ];
                    path1 = Quiet[FindShortestPath[directed, initExprs[[1]], best]];
                    path2 = Quiet[FindShortestPath[directed, initExprs[[2]], best]];
                    proofPath = DeleteDuplicates[Join[path1, path2]];
                    proofEdges = Join[
                        If[ListQ[path1] && Length[path1] > 1, DirectedEdge[#[[1]], #[[2]]]& /@ Partition[path1, 2, 1], {}],
                        If[ListQ[path2] && Length[path2] > 1, DirectedEdge[#[[1]], #[[2]]]& /@ Partition[path2, 2, 1], {}]
                    ]
                ]
            ]
        ]
    ];
    <|"proofPath" -> proofPath, "proofEdges" -> proofEdges|>
]

equationalVertexStyles[vertices_, initExprs_, proofPath_] := Map[
    Function[v,
        v -> Which[
            v === True,
                Directive[$InductiveProofColors["IdentityFill"], EdgeForm[$InductiveProofColors["IdentityStroke"]]]
            ,
            v === initExprs[[1]],
                Directive[Opacity[0.85], $axiomHue, EdgeForm[$axiomVertexEdge]]
            ,
            Length[initExprs] >= 2 && v === initExprs[[2]],
                Directive[Opacity[0.85], $theoremHue, EdgeForm[$theoremFrameColor]]
            ,
            MemberQ[proofPath, v],
                Directive[Opacity[0.7], $InductiveProofColors["PathHighlight"], EdgeForm[$equationalEdgeColor]]
            ,
            True,
                Directive[Opacity[0.5], $theoremHue, EdgeForm[$theoremFrameColor]]
        ]
    ]
    ,
    vertices
]

equationalEdgeStyles[allEdges_, proofEdges_] := Map[
    Function[e,
        e -> If[MemberQ[proofEdges, e], Directive[Red, AbsoluteThickness[2]], $equationalEdgeColor]
    ]
    ,
    allEdges
]

equationalVertexLabels[vertices_, vertexLabelsOption_] := Switch[ vertexLabelsOption,
    "Tooltip",
        Map[
            With[{v = #},
                v -> Placed[renderMultiwayExpression[v], Tooltip]
            ]&
            ,
            vertices
        ]
    ,
    _,
        Map[# -> None&, vertices]
]

equationalVertexShapes[vertices_, initExprs_, proofPath_] := Map[
    With[{v = #},
        # -> With[{
                background = Which[
                    MemberQ[initExprs, v],
                        $axiomBackground
                    ,
                    MemberQ[proofPath, v],
                        $pathHighlightBackground
                    ,
                    True,
                        $theoremBackground
                ]
            },
                (Inset[styledBox[renderMultiwayExpression[v], background], #1]&)
            ]
    ]&
    ,
    vertices
]

equationalSeedCallout[v_, raw_, background_] := v -> {RenderConfiguration[raw], background}

equationalGraphResult[
    vertices_,
    allEdges_,
    initExprs_,
    initExprsRaw_,
    proof_,
    labeled_,
    vertexLabelsOption_,
    arrowSize_,
    calloutMaxWidth_
] := Module[{
    proofPath = proof["proofPath"],
    proofEdges = proof["proofEdges"],
    vertexSize = Min[0.45, 3.0 / Sqrt[Max[Length[vertices], 4]]],
    graphOptions,
    fullGraph,
    components,
    result
},
    graphOptions = {
        VertexStyle -> equationalVertexStyles[vertices, initExprs, proofPath]
        ,
        VertexLabels -> equationalVertexLabels[vertices, vertexLabelsOption]
        ,
        VertexSize -> vertexSize
        ,
        EdgeStyle -> equationalEdgeStyles[allEdges, proofEdges]
        ,
        EdgeShapeFunction -> With[{markedEdges = proofEdges, setback = 0.45 vertexSize, head = arrowSize},
            Function[{pts, e},
                Join[
                    If[MemberQ[markedEdges, e], {Red, AbsoluteThickness[2], Arrowheads[1.6 head]}, {Arrowheads[head]}],
                    {Arrow[pts, setback]}
                ]
            ]
        ]
        ,
        GraphLayout -> "SpringElectricalEmbedding"
        ,
        PerformanceGoal -> "Quality"
        ,
        ImageSize -> Large
    };
    graphOptions = If[ labeled,
        Append[graphOptions, VertexShapeFunction -> equationalVertexShapes[vertices, initExprs, proofPath]]
        ,
        graphOptions
    ];
    fullGraph = Graph[vertices, allEdges, graphOptions];
    components = ConnectedComponents[UndirectedGraph[fullGraph]];
    result = If[ Length[components] == 2 && Length[initExprs] >= 2,
        Module[{leftComponent, rightComponent, leftGraph, rightGraph},
            {leftComponent, rightComponent} = If[ MemberQ[components[[1]], initExprs[[1]]],
                {components[[1]], components[[2]]}
                ,
                {components[[2]], components[[1]]}
            ];
            leftGraph = Subgraph[fullGraph, leftComponent, GraphLayout -> "SpringElectricalEmbedding", ImageSize -> Medium];
            rightGraph = Subgraph[fullGraph, rightComponent, GraphLayout -> "SpringElectricalEmbedding", ImageSize -> Medium];
            If[ ! labeled,
                leftGraph = attachSeedCallouts[
                    leftGraph,
                    {equationalSeedCallout[initExprs[[1]], initExprsRaw[[1]], $axiomBackground]},
                    calloutMaxWidth
                ];
                rightGraph = attachSeedCallouts[
                    rightGraph,
                    {equationalSeedCallout[initExprs[[2]], initExprsRaw[[2]], $theoremBackground]},
                    calloutMaxWidth
                ]
            ];
            GraphicsRow[{leftGraph, rightGraph}, Spacings -> 20]
        ]
        ,
        fullGraph
    ];
    If[ Length[initExprs] >= 2 && MatchQ[result, _Graph] && ! labeled,
        attachSeedCallouts[
            result
            ,
            {
                equationalSeedCallout[initExprs[[1]], initExprsRaw[[1]], $axiomBackground],
                equationalSeedCallout[initExprs[[2]], initExprsRaw[[2]], $theoremBackground]
            }
            ,
            calloutMaxWidth
        ]
        ,
        result
    ]
]

Options[MultiwayEquationalGraph] = {
    "CriticalPairs" -> False,
    "VertexLabels" -> None,
    "WellFormedOnly" -> True,
    "ArrowSize" -> Automatic,
    "Oriented" -> False,
    "Ordering" -> "LeafCount",
    "CalloutMaxWidth" -> 240
}

MultiwayEquationalGraph[
    axioms_List, initExprsRaw_List, steps_Integer, style_String : "ProofGraph", opts : OptionsPattern[]
] := Module[{
    rules,
    accept,
    simp = $emptyRunSimplification,
    labeled,
    initExprs,
    evolution,
    allExprs,
    allEdges,
    vertices,
    proof
},
    labeled = style =!= "ProofGraph" || MatchQ[OptionValue["VertexLabels"], True | "Boxed"];
    rules = multiwayRulesFromAxioms[axioms, OptionValue["Oriented"], OptionValue["Ordering"], OptionValue["CriticalPairs"]];
    accept[t_] := ! OptionValue["WellFormedOnly"] || wellFormedQ[t];
    initExprs = initExprsRaw //. simp;
    evolution = evolveMultiwayCloud[initExprs, rules, accept, steps];
    allExprs = evolution["allExprs"];
    allEdges = DeleteDuplicates[evolution["allEdges"]];
    vertices = DeleteDuplicates[
        Join[initExprs, Cases[allEdges, DirectedEdge[s_, _] :> s], Cases[allEdges, DirectedEdge[_, t_] :> t]]
    ];
    proof = equationalProofPath[vertices, allEdges, initExprs];
    equationalGraphResult[
        vertices,
        allEdges,
        initExprs,
        initExprsRaw,
        proof,
        labeled,
        OptionValue["VertexLabels"],
        OptionValue["ArrowSize"] /. Automatic -> 0.012,
        OptionValue["CalloutMaxWidth"]
    ]
]

multiwayDistance[lhsE_, rhsE_, axioms_, steps_, wellFormed_ : True] := Module[{
    rules = Flatten[axiomToMultiwayRules /@ axioms],
    simp = $emptyRunSimplification,
    okQ,
    lhs,
    rhs,
    evolve,
    seed,
    final
},
    okQ[t_] := ! wellFormed || wellFormedQ[t];
    lhs = lhsE //. simp;
    rhs = rhsE //. simp;
    evolve[{allExprs_, allEdges_, frontier_}, _] := Module[{res = multiwayStep[frontier, rules], newExprs, newEdges, fresh},
        newExprs = Select[res[[1]] //. simp, okQ];
        newEdges = Select[
            res[[2]] /. DirectedEdge[a_, b_] :> DirectedEdge[a //. simp, b //. simp],
            #[[1]] =!= #[[2]] && okQ[#[[1]]] && okQ[#[[2]]]&
        ];
        fresh = Complement[newExprs, allExprs];
        {Join[allExprs, fresh], Join[allEdges, newEdges], fresh}
    ];
    seed = DeleteDuplicates[{lhs, rhs}];
    final = Fold[evolve, {seed, {}, seed}, Range[steps]];
    GraphDistance[Graph[final[[1]], DeleteDuplicates[final[[2]]] /. DirectedEdge -> UndirectedEdge], lhs, rhs]
]

attachSeedCallouts[g_Graph, specs_List, maxW_ : 240] := Module[{
    coords2 = GraphEmbedding[g],
    vl2 = VertexList[g],
    xs2,
    ys2,
    sx,
    sy,
    sp,
    cornerOff,
    cornerAnch,
    cornerCtr,
    boxFor,
    mkC,
    near,
    c1,
    c2,
    cs,
    rs,
    topQ,
    padT,
    padB
},
    xs2 = MinMax[coords2[[All, 1]]];
    ys2 = MinMax[coords2[[All, 2]]];
    sx = xs2[[2]] - xs2[[1]] + 1;
    sy = ys2[[2]] - ys2[[1]] + 1;
    sp = Max[sx, sy];
    cornerOff["TR"] = {xs2[[2]] + 0.05 * sp, ys2[[2]] + 0.08 * sp};
    cornerOff["TL"] = {xs2[[1]] - 0.05 * sp, ys2[[2]] + 0.08 * sp};
    cornerOff["BL"] = {xs2[[1]] - 0.05 * sp, ys2[[1]] - 0.08 * sp};
    cornerOff["BR"] = {xs2[[2]] + 0.05 * sp, ys2[[1]] - 0.08 * sp};
    cornerAnch["TR"] = {Right, Bottom};
    cornerAnch["TL"] = {Left, Bottom};
    cornerAnch["BL"] = {Left, Top};
    cornerAnch["BR"] = {Right, Top};
    cornerCtr["TR", w_, h_] := Offset[{-w / 2, h / 2}, cornerOff["TR"]];
    cornerCtr["TL", w_, h_] := Offset[{w / 2, h / 2}, cornerOff["TL"]];
    cornerCtr["BL", w_, h_] := Offset[{w / 2, -h / 2}, cornerOff["BL"]];
    cornerCtr["BR", w_, h_] := Offset[{-w / 2, -h / 2}, cornerOff["BR"]];
    boxFor[disp_, bg_] := styledBox[disp, bg];
    mkC[atV_, {disp_, bg_}, corner_] := Module[{idx, pos, bx, dims, mag},
        idx = FirstPosition[vl2, atV];
        If[ MissingQ[idx],
            {{}, {0, 0}}
            ,
            pos = coords2[[idx[[1]]]];
            bx = boxFor[disp, bg];
            dims = N[Take[Rasterize[bx, "BoundingBox"], 2]];
            mag = N[Min[1, maxW / Max[dims[[1]], 1]]];
            If[ mag < 1,
                bx = Image[Rasterize[bx, ImageResolution -> 216], ImageSize -> mag * dims];
                dims = mag * dims
            ];
            {
                {
                    $InductiveProofColors["CalloutConnector"],
                    AbsoluteThickness[1.0],
                    Line[{pos, cornerCtr[corner, dims[[1]], dims[[2]]]}],
                    Inset[bx, cornerOff[corner], cornerAnch[corner]]
                }
                ,
                dims
            }
        ]
    ];
    near[v_, csL_List] := Module[{idx = FirstPosition[vl2, v], pp},
        If[ MissingQ[idx],
            First[csL]
            ,
            pp = coords2[[idx[[1]]]];
            First[MinimalBy[csL, Norm[pp - cornerOff[#]]&]]
        ]
    ];
    c1 = near[specs[[1, 1]], {"TR", "TL", "BL", "BR"}];
    c2 = If[ Length[specs] < 2,
        None
        ,
        near[specs[[2, 1]], If[StringTake[c1, 1] === "T", {"BL", "BR"}, {"TR", "TL"}]]
    ];
    cs = If[c2 === None, {c1}, {c1, c2}];
    rs = Table[mkC[specs[[i, 1]], specs[[i, 2]], cs[[i]]], {i, Length[cs]}];
    topQ[c_] := StringTake[c, 1] === "T";
    padT = 14 + Max[Prepend[Table[If[topQ[cs[[i]]], rs[[i, 2, 2]], 0], {i, Length[cs]}], 0]];
    padB = 14 + Max[Prepend[Table[If[! topQ[cs[[i]]], rs[[i, 2, 2]], 0], {i, Length[cs]}], 0]];
    Show[
        g,
        Epilog -> Join @@ Map[First, rs],
        PlotRange -> All,
        PlotRangePadding -> {{0.08 * sp, 0.08 * sp}, {0.11 * sp, 0.11 * sp}},
        ImagePadding -> {{14, 14}, {padB, padT}}
    ]
]

rawAxiomsForMachine[ru_, st_ : 2] := Module[{rules = DecodeTuringMachineRules[ru, st, 2]},
    Join[
        encodeTransitionAxioms[rules],
        Map[ForAll[x, seq[seq[x, bnd], #] == seq[x, bnd]]&, DeleteDuplicates[rules[[All, 1, 1]]]],
        onesRunDefinitions,
        zerosRunDefinitions
    ]
]

$tmShape = <|
    453 -> {2, 2},
    445 -> {2, 2},
    1512 -> {2, 2},
    137893 -> {3, 2},
    161601 -> {3, 2},
    234189 -> {3, 2},
    237101 -> {3, 2},
    238270 -> {3, 2},
    248514 -> {3, 2},
    727124 -> {3, 2},
    744446 -> {3, 2},
    745401 -> {3, 2},
    1243838 -> {3, 2},
    1721913 -> {3, 2},
    2717225 -> {3, 2}
|>

tmStatesFor[ru_] := If[KeyExistsQ[$tmShape, ru], $tmShape[ru][[1]], 2]

$buggyMachines = {
    137893,
    449,
    457,
    465,
    473,
    481,
    489,
    497,
    505,
    1480,
    1481,
    1482,
    1483,
    1484,
    1485,
    1486,
    1487,
    2501,
    1505
}

multiwaySystemFor[ru_] := multiwaySystemFor[ru] = Module[{st = tmStatesFor[ru], p, eq},
    If[ MemberQ[$buggyMachines, ru],
        eq = seq[seq[ones[succ[n], seq[x, s0]], qA], bnd] == seq[zeros[succ[n], seq[x, s1]], bnd];
        <|
            "Axioms" -> rawAxiomsForMachine[ru, st],
            "IH" -> {},
            "Rows" -> {},
            "StepEq" -> eq,
            "StepSeeds" -> {eq[[1]], eq[[2]]},
            "BaseSeeds" -> ({eq[[1]], eq[[2]]} /. succ[n] -> zero),
            "RawAxioms" -> rawAxiomsForMachine[ru, st]
        |>
        ,
        p = cachedProofFor[ru];
        <|
            "Axioms" -> p["Axioms"],
            "IH" -> {p["IH"]},
            "Rows" -> derivedLemmaAxioms[p["StepProof"]],
            "StepEq" -> p["StepGoal"],
            "StepSeeds" -> {p["StepGoal"][[1]], p["StepGoal"][[2]]},
            "BaseSeeds" -> {p["BaseGoal"][[1]], p["BaseGoal"][[2]]},
            "RawAxioms" -> rawAxiomsForMachine[ru, st]
        |>
    ]
]

multiwayRulesFromAxioms[axioms_, oriented_, ordering_, criticalPairs_] := Module[{weight = If[ordering === "RunUnfold", runUnfoldWeight, LeafCount], rules},
    rules = If[ oriented,
        Flatten[Map[axiomToOrientedRules[#, weight]&, axioms]]
        ,
        Flatten[axiomToMultiwayRules /@ axioms]
    ];
    If[ criticalPairs,
        Module[{criticalPairRules = generateCriticalPairs[axioms]},
            If[ oriented,
                criticalPairRules = Select[criticalPairRules, weight[#[[1]] /. Verbatim[Pattern][s_, _] :> s] >= weight[#[[2]]]&]
            ];
            rules = DeleteDuplicates[Join[rules, criticalPairRules]]
        ]
    ];
    rules
]

evolveMultiwayCloud[initExprs_, rules_, accept_, steps_] := Module[{simp = $emptyRunSimplification},
    Fold[
        Function[{state, step},
            Module[{result = multiwayStep[state["frontier"], rules], newExprs, newEdges, advanced},
                newExprs = Select[result[[1]] //. simp, accept];
                newEdges = Select[
                    result[[2]] /. DirectedEdge[a_, b_] :> DirectedEdge[a //. simp, b //. simp],
                    #[[1]] =!= #[[2]] && accept[#[[1]]] && accept[#[[2]]]&
                ];
                advanced = Complement[newExprs, state["allExprs"]];
                <|
                    "allExprs" -> Join[state["allExprs"], advanced],
                    "allEdges" -> Join[state["allEdges"], newEdges],
                    "frontier" -> advanced
                |>
            ]
        ]
        ,
        <|"allExprs" -> initExprs, "allEdges" -> {}, "frontier" -> initExprs|>
        ,
        Range[steps]
    ]
]

geodesicBetween[allExprs_, allEdges_, initExprs_] := Module[{path},
    path = Which[ 
        Length[initExprs] >= 2,
            Quiet[
                FindShortestPath[Graph[allExprs, allEdges /. DirectedEdge -> UndirectedEdge], initExprs[[1]], initExprs[[2]]]
            ]
        ,
        MemberQ[allExprs, True],
            Quiet[FindShortestPath[Graph[allExprs, allEdges], initExprs[[1]], True]]
        ,
        True,
            {}
    ];
    If[! ListQ[path] || Length[path] < 2, path = {}];
    <|
        "path" -> path,
        "pathPairs" -> If[path =!= {}, Map[Sort, Partition[path, 2, 1]], {}],
        "length" -> If[path === {}, ∞, Length[path] - 1]
    |>
]

firstOrientationByKey[edges_] := Fold[
    Function[{oriented, e},
        With[{key = Sort[{e[[1]], e[[2]]}]},
            If[KeyExistsQ[oriented, key], oriented, Append[oriented, key -> {e[[1]], e[[2]]}]]
        ]
    ]
    ,
    <||>
    ,
    edges
]

geodesicVertexSize[allExprs_, allEdges_] := Module[{
    span = Max[1., Max[Map[Abs[Max[#] - Min[#]]&, Transpose[GraphEmbedding[Graph[allExprs, allEdges]]]]]]
},
    Min[0.025 span, 3.0 / Sqrt[Max[Length[allExprs], 4]]]
]

geodesicVertexStyles[allExprs_, initExprs_, path_] := Map[
    Function[v,
        v -> Which[
            MemberQ[initExprs, v],
                $axiomVertexStyle
            ,
            MemberQ[path, v],
                Directive[Opacity[0.7], $pathHighlight, EdgeForm[frameColorFor[$pathHighlight]]]
            ,
            True,
                Directive[Opacity[0.5], $theoremHue, EdgeForm[$theoremFrameColor]]
        ]
    ]
    ,
    allExprs
]

geodesicEdgeStyles[allEdges_, pathPairs_, arrowSizeCloud_] := Map[
    Function[e,
        e -> If[ MemberQ[pathPairs, Sort[{e[[1]], e[[2]]}]],
                Directive[Red, AbsoluteThickness[2], Arrowheads[1.6 arrowSizeCloud]]
                ,
                Directive[$equationalEdgeColor, Arrowheads[1.6 arrowSizeCloud]]
            ]
    ]
    ,
    allEdges
]

cloudEdgeShapes[allEdges_, path_, pathPairs_, arrowSizeProof_, arrowSizeCloud_, vertexSize_] := Module[{
    directedPath = If[Length[path] > 1, Map[{#[[1]], #[[2]]}&, Partition[path, 2, 1]], {}],
    firstOrientation = firstOrientationByKey[allEdges]
},
    Map[
        Function[e,
            e -> Which[ 
                    MemberQ[directedPath, {e[[1]], e[[2]]}],
                        With[{a = arrowSizeProof, sb = 0.45 vertexSize},
                            ({Arrowheads[a], Arrow[#1, sb]}&)
                        ]
                    ,
                    MemberQ[pathPairs, Sort[{e[[1]], e[[2]]}]],
                        ({}&)
                    ,
                    firstOrientation[Sort[{e[[1]], e[[2]]}]] === {e[[1]], e[[2]]},
                        With[{a = arrowSizeCloud, sb = 0.45 vertexSize},
                            ({Arrowheads[a], Arrow[#1, sb]}&)
                        ]
                    ,
                    True,
                        ({}&)
                ]
        ]
        ,
        allEdges
    ]
]

geodesicBoxedVertexShapes[allExprs_, initExprs_, path_] := Map[
    With[{v = #},
        v -> (
                With[{
                    background = Which[
                        MemberQ[initExprs, v],
                            $axiomBackground
                        ,
                        MemberQ[path, v],
                            $pathHighlightBackground
                        ,
                        True,
                            $theoremBackground
                    ]
                },
                    Inset[
                        styledBox[
                            Which[ 
                                v === True,
                                    $qedSymbol
                                ,
                                MatchQ[v, _Equal],
                                    renderGraphEquation[HoldForm @@ {v}]
                                ,
                                True,
                                    RenderConfiguration[v]
                            ]
                            ,
                            background
                        ]
                        ,
                        #1
                    ]
                ]&
            )
    ]&
    ,
    allExprs
]

attachGeodesicCallouts[g_, initExprs_, allExprs_, calloutMaxWidth_] := Module[{second, specs},
    second = If[Length[initExprs] >= 2, initExprs[[2]], If[MemberQ[allExprs, True], True, None]];
    specs = Join[
        {
            initExprs[[1]] -> {
                    If[ MatchQ[initExprs[[1]], _Equal],
                        renderGraphEquation[HoldForm @@ {initExprs[[1]]}]
                        ,
                        RenderConfiguration[initExprs[[1]]]
                    ]
                    ,
                    $theoremBackground
                }
        }
        ,
        If[ second === None,
            {}
            ,
            {
                second -> If[ second === True,
                        {$qedSymbol, $InductiveProofColors["IdentityBackground"]}
                        ,
                        {renderGraphEquation[HoldForm @@ {second}], $theoremBackground}
                    ]
            }
        ]
    ];
    attachSeedCallouts[g, specs, calloutMaxWidth]
]

Options[MultiwayGeodesicGraph] = {
    "CriticalPairs" -> False,
    "WellFormedOnly" -> True,
    "ShowLength" -> False,
    "VertexLabels" -> Automatic,
    "Oriented" -> False,
    "Ordering" -> "LeafCount",
    "CloudUndirected" -> False,
    "ArrowSize" -> Automatic,
    "CalloutMaxWidth" -> 240
}

MultiwayGeodesicGraph[axioms_List, initExprsRaw_List, steps_Integer, opts : OptionsPattern[]] := Module[{
    rules,
    accept,
    simp = $emptyRunSimplification,
    initExprs,
    evolution,
    allExprs,
    allEdges,
    geodesic,
    path,
    pathPairs,
    len,
    autoLabel,
    vertexSize,
    arrowSizeProof,
    arrowSizeCloud,
    g
},
    rules = multiwayRulesFromAxioms[axioms, OptionValue["Oriented"], OptionValue["Ordering"], OptionValue["CriticalPairs"]];
    accept[t_] := ! OptionValue["WellFormedOnly"] || wellFormedQ[t];
    initExprs = DeleteDuplicates[initExprsRaw //. simp];
    evolution = evolveMultiwayCloud[initExprs, rules, accept, steps];
    allExprs = evolution["allExprs"];
    allEdges = DeleteDuplicates[evolution["allEdges"]];
    geodesic = geodesicBetween[allExprs, allEdges, initExprs];
    path = geodesic["path"];
    pathPairs = geodesic["pathPairs"];
    len = geodesic["length"];
    {arrowSizeProof, arrowSizeCloud} = OptionValue["ArrowSize"] /. Automatic -> {0.014, 0.009};
    vertexSize = geodesicVertexSize[allExprs, allEdges];
    autoLabel = MatchQ[OptionValue["VertexLabels"], True | "Boxed"];
    g = Graph[
        allExprs
        ,
        allEdges
        ,
        If[ TrueQ[OptionValue["CloudUndirected"]],
            EdgeShapeFunction -> cloudEdgeShapes[allEdges, path, pathPairs, arrowSizeProof, arrowSizeCloud, vertexSize]
            ,
            Unevaluated[Sequence[]]
        ]
        ,
        VertexStyle -> geodesicVertexStyles[allExprs, initExprs, path]
        ,
        VertexLabels -> None
        ,
        VertexSize -> vertexSize
        ,
        EdgeStyle -> geodesicEdgeStyles[allEdges, pathPairs, arrowSizeCloud]
        ,
        If[ autoLabel,
            VertexShapeFunction -> geodesicBoxedVertexShapes[allExprs, initExprs, path]
            ,
            Unevaluated[Sequence[]]
        ]
        ,
        GraphLayout -> "SpringElectricalEmbedding"
        ,
        PerformanceGoal -> "Quality"
        ,
        ImageSize -> Large
    ];
    If[! autoLabel, g = attachGeodesicCallouts[g, initExprs, allExprs, OptionValue["CalloutMaxWidth"]]];
    If[TrueQ[OptionValue["ShowLength"]], Labeled[g, Row[{"geodesic length: ", len}], Top], g]
]

washColor[c_, washOpacity_] := switchedColor[Blend[{#, Red}, washOpacity]&, c]

tokenEventAxiomVertex[trip_, collapse_] := {"MWAx", If[collapse, trip[[2]], trip]}

tokenEventIndexedRules[axioms_, oriented_, ordering_, criticalPairs_] := Module[{weight = If[ordering === "RunUnfold", runUnfoldWeight, LeafCount], expanded},
    expanded = If[ criticalPairs,
        DeleteDuplicates[
            Join[axioms, Map[(#[[1]] /. Verbatim[Pattern][s_, _] :> s) == #[[2]]&, generateCriticalPairs[axioms]]]
        ]
        ,
        axioms
    ];
    {
        expanded
        ,
        Flatten[
            MapIndexed[
                Function[{ax, ix},
                    Map[{ix[[1]], #}&, If[oriented, axiomToOrientedRules[ax, weight], axiomToMultiwayRules[ax]]]
                ]
                ,
                expanded
            ]
            ,
            1
        ]
    }
]

tokenEventTargets[src_, rule_] := DeleteDuplicates[
    Join[
        With[{whole = Replace[src, rule]},
            If[whole =!= src, {whole}, {}]
        ]
        ,
        Map[
            Function[pos,
                With[{subterm = Extract[src, pos], replaced = Replace[Extract[src, pos], rule]},
                    If[ replaced =!= subterm,
                        With[{rewritten = ReplacePart[src, pos -> replaced]},
                            If[rewritten =!= src, rewritten, Nothing]
                        ]
                        ,
                        Nothing
                    ]
                ]
            ]
            ,
            Position[src, _, {1, Infinity}, Heads -> False]
        ]
    ]
]

tokenEventTripsFrom[src_, indexedRules_, simp_, accept_] := Flatten[
    Map[
        Function[indexed,
            With[{axiomIndex = indexed[[1]], rule = indexed[[2]]},
                Map[
                    {src, axiomIndex, #}&,
                    Select[Map[# //. simp&, tokenEventTargets[src, rule]], # =!= src && accept[#]&]
                ]
            ]
        ]
        ,
        indexedRules
    ]
    ,
    1
]

tokenEventEvolve[initExprs_, indexedRules_, simp_, accept_, steps_, maxStates_] := Module[{final},
    final = Fold[
        Function[{state, d},
            Module[{
                stepTrips = Flatten[Map[tokenEventTripsFrom[#, indexedRules, simp, accept]&, state["frontier"]], 1],
                newExprs
            },
                newExprs = DeleteDuplicates[Select[Map[Last, stepTrips], ! MemberQ[state["allExprs"], #]&]];
                <|
                    "allExprs" -> Join[state["allExprs"], newExprs],
                    "trips" -> Join[state["trips"], stepTrips],
                    "frontier" -> If[Length[state["allExprs"]] + Length[newExprs] >= maxStates, {}, newExprs]
                |>
            ]
        ]
        ,
        <|"allExprs" -> initExprs, "trips" -> {}, "frontier" -> initExprs|>
        ,
        Range[steps]
    ];
    <|"allExprs" -> final["allExprs"], "trips" -> DeleteDuplicates[final["trips"]]|>
]

tokenEventProofPath[initExprs_, allExprs_, trips_] := Module[{path, pathPairs, pathTrips},
    path = Which[ 
        Length[initExprs] >= 2,
            Quiet[
                FindShortestPath[
                    Graph[allExprs, DeleteDuplicates[Map[UndirectedEdge[#[[1]], #[[3]]]&, trips]]],
                    initExprs[[1]],
                    initExprs[[2]]
                ]
            ]
        ,
        MemberQ[allExprs, True],
            Quiet[
                FindShortestPath[
                    Graph[allExprs, DeleteDuplicates[Map[DirectedEdge[#[[1]], #[[3]]]&, trips]]],
                    First[initExprs],
                    True
                ]
            ]
        ,
        True,
            {}
    ];
    If[! ListQ[path] || Length[path] < 2, path = {}];
    pathPairs = If[path === {}, {}, Partition[path, 2, 1]];
    pathTrips = Flatten[
        Map[
            Function[pair,
                Take[Select[trips, {#[[1]], #[[3]]} === pair || {#[[3]], #[[1]]} === pair&], UpTo[1]]
            ]
            ,
            pathPairs
        ]
        ,
        1
    ];
    <|"path" -> path, "pathTrips" -> pathTrips|>
]

tokenEventStateColors[allExprs_, initExprs_, path_, hl_, fadeOp_, washOpacity_] := Map[
    Function[v,
        {"MWState", v} -> Module[{onPath = MemberQ[path, v], baseColor},
            baseColor = Which[
                v === True,
                    $theoremHue
                ,
                Length[initExprs] >= 2 && v === initExprs[[2]],
                    $theoremHue
                ,
                MemberQ[initExprs, v],
                    $axiomHue
                ,
                True,
                    $theoremHue
            ];
            Which[
                hl === "Fade",
                    {
                        Directive[Opacity[If[onPath, 1, fadeOp]], baseColor],
                        If[onPath, frameColorFor[baseColor], Opacity[fadeOp, frameColorFor[baseColor]]]
                    }
                ,
                onPath && hl === "Wash",
                    {
                        Directive[Opacity[0.85], washColor[baseColor, washOpacity]],
                        frameColorFor[washColor[baseColor, washOpacity]]
                    }
                ,
                onPath && v =!= True && ! MemberQ[initExprs, v],
                    {Directive[Opacity[0.7], $pathHighlight], frameColorFor[$pathHighlight]}
                ,
                v === True || (Length[initExprs] >= 2 && v === initExprs[[2]]),
                    {Directive[Opacity[0.85], baseColor], $theoremFrameColor}
                ,
                MemberQ[initExprs, v],
                    {Directive[Opacity[0.7], baseColor], $axiomVertexEdge}
                ,
                True,
                    {Directive[Opacity[0.7], baseColor], $theoremFrameColor}
            ]
        ]
    ]
    ,
    allExprs
]

tokenEventEventColors[evs_, pathTrips_, hl_, fadeOp_, washOpacity_] := Map[
    Function[ev,
        ev -> Which[ 
            hl === "Fade",
                {
                    Directive[Opacity[If[MemberQ[pathTrips, ev[[2]]], 1, fadeOp]], $defaultEventFill],
                    $defaultEventStroke
                }
            ,
            hl === "Wash" && MemberQ[pathTrips, ev[[2]]],
                {
                    washColor[$defaultEventFill, washOpacity], frameColorFor[washColor[$defaultEventFill, washOpacity]]
                }
            ,
            True,
                {$defaultEventFill, $defaultEventStroke}
        ]
    ]
    ,
    evs
]

tokenEventAxiomColors[axVs_, pathAxVs_, hl_, fadeOp_, washOpacity_] := Map[
    Function[av,
        av -> Which[
                hl === "Fade",
                    {
                        Directive[Opacity[If[MemberQ[pathAxVs, av], 1, fadeOp]], $axiomHue],
                        $axiomVertexEdge
                    }
                ,
                hl === "Wash" && MemberQ[pathAxVs, av],
                    {
                        Directive[Opacity[0.7], washColor[$axiomHue, washOpacity]],
                        frameColorFor[washColor[$axiomHue, washOpacity]]
                    }
                ,
                True,
                    {Directive[Opacity[0.7], $axiomHue], $axiomVertexEdge}
            ]
    ]
    ,
    axVs
]

tokenEventEdgeStyles[edges_, redEdges_, washAxE_, hl_, asz_, fadeOp_, washOpacity_] := Map[
    Function[e,
        e -> Which[ 
            hl === "Fade" && MemberQ[redEdges, e],
                Directive[$equationalEdgeColor, AbsoluteThickness[2], Arrowheads[1.6 asz]]
            ,
            hl === "Fade",
                Directive[Opacity[fadeOp], $equationalEdgeColor, Arrowheads[asz]]
            ,
            MemberQ[redEdges, e] && hl === "Wash",
                Directive[washColor[$equationalEdgeColor, washOpacity], AbsoluteThickness[2.2], Arrowheads[1.6 asz]]
            ,
            MemberQ[redEdges, e],
                Directive[Red, AbsoluteThickness[2], Arrowheads[2 asz]]
            ,
            hl === "Wash" && MemberQ[washAxE, e],
                Directive[washColor[$equationalEdgeColor, washOpacity], AbsoluteThickness[1.4], Arrowheads[asz]]
            ,
            True,
                Directive[$equationalEdgeColor, Arrowheads[asz]]
        ]
    ]
    ,
    edges
]

tokenEventLabeledShapes[allExprs_, axVs_, evs_, initExprs_, path_, hl_, washOpacity_, axioms_, collapse_] := Join[
    Map[
        Function[v,
            {"MWState", v} -> Which[ 
                    v === True,
                        equationVertexShape[$qedSymbol, False, 3]
                    ,
                    MemberQ[initExprs, v],
                        equationVertexShape[renderGraphEquation[HoldForm @@ {v}], True, 3]
                    ,
                    MemberQ[path, v],
                        With[{
                            background = If[ hl === "Wash",
                                washColor[$theoremBackground, 0.6 washOpacity]
                                ,
                                $pathHighlightBackground
                            ]
                        },
                            (Inset[styledBox[renderGraphEquation[HoldForm @@ {v}], background], #1]&)
                        ]
                    ,
                    True,
                        equationVertexShape[renderGraphEquation[HoldForm @@ {v}], False, 3]
                ]
        ]
        ,
        allExprs
    ]
    ,
    Map[
        Function[av,
            av -> equationVertexShape[renderGraphEquation[HoldForm @@ {forAllBody[axioms[[If[collapse, av[[2]], av[[2, 2]]]]]]}], True]
        ]
        ,
        axVs
    ]
    ,
    Map[# -> eventVertexShape[8]&, evs]
]

tokenEventDiskShapes[verts_, vcols_, vertexScale_, sizeByLeafCount_] := Module[{baseSize, sizeFor},
    baseSize = vertexScale Min[15., 130. / Sqrt[Max[Length[verts], 1]]];
    sizeFor[{"MWState", t_}] := If[TrueQ[sizeByLeafCount], If[t === True, 10., vertexScale 4.2 Sqrt[LeafCount[t]]], baseSize];
    sizeFor[{"MWEv", _}] := 0.5 baseSize;
    sizeFor[{"MWAx", _}] := 0.75 baseSize;
    Map[
        Function[colored,
            colored[[1]] -> discVertex[colored[[2, 1]], colored[[2, 2]], sizeFor[colored[[1]]]]
        ]
        ,
        vcols
    ]
]

tokenEventCoordinates[verts_, edges_, allExprs_, initExprs_, pinCoords_] := Module[{default, pinAssoc, pins},
    default = multiwayPinnedLayeredCoordinates[
        verts
        ,
        edges
        ,
        {"MWState", First[initExprs]}
        ,
        Which[ 
            Length[initExprs] >= 2,
                {"MWState", initExprs[[2]]}
            ,
            MemberQ[allExprs, True],
                {"MWState", True}
            ,
            True,
                None
        ]
    ];
    If[ pinCoords === {} || pinCoords === None,
        {default, Automatic}
        ,
        pinAssoc = Association[pinCoords];
        pins = DeleteCases[
            Map[
                Function[state,
                    Module[{
                        key = Which[ 
                            KeyExistsQ[pinAssoc, state],
                                state
                            ,
                            MatchQ[state, _Equal] && KeyExistsQ[pinAssoc, state[[2]] == state[[1]]],
                                state[[2]] == state[[1]]
                            ,
                            True,
                                None
                        ]
                    },
                        If[key === None, Nothing, {"MWState", state} -> pinAssoc[key]]
                    ]
                ]
                ,
                allExprs
            ]
            ,
            Nothing
        ];
        If[ Length[pins] >= 2,
            {pins, {"SpringElectricalEmbedding", "PinnedVertices" -> pins[[All, 1]]}}
            ,
            {default, Automatic}
        ]
    ]
]

Options[MultiwayTokenEventGraph] = {
    "WellFormedOnly" -> True,
    "Labeled" -> False,
    "CollapseAxioms" -> False,
    "ShowAxioms" -> True,
    "SizeByLeafCount" -> False,
    "HighlightStyle" -> "Red",
    "WashOpacity" -> 0.5,
    "FadeOpacity" -> 0.13,
    "PinProof" -> False,
    "ProofLayout" -> "LayeredDigraphEmbedding",
    "PinCoords" -> {},
    "MaxStates" -> Infinity,
    "VertexScale" -> 1,
    "ArrowSize" -> 0.011,
    "Oriented" -> False,
    "Ordering" -> "LeafCount",
    "CriticalPairs" -> False
}

MultiwayTokenEventGraph[axioms_List, initExprsRaw_List, steps_Integer, OptionsPattern[]] := Module[{
    collapse = TrueQ[OptionValue["CollapseAxioms"]],
    hl = OptionValue["HighlightStyle"],
    asz = OptionValue["ArrowSize"],
    fadeOp = OptionValue["FadeOpacity"],
    washOpacity = OptionValue["WashOpacity"],
    simp = $emptyRunSimplification,
    accept,
    expandedAxioms,
    indexedRules,
    initExprs,
    evolution,
    allExprs,
    trips,
    proof,
    path,
    pathTrips,
    redEdges,
    pathAxVs,
    washAxE,
    evs,
    axVs,
    verts,
    edges,
    vcols,
    vstyles,
    coords,
    glayoutOpt
},
    accept[t_] := ! OptionValue["WellFormedOnly"] || wellFormedQ[t];
    {expandedAxioms, indexedRules} = tokenEventIndexedRules[axioms, OptionValue["Oriented"], OptionValue["Ordering"], OptionValue["CriticalPairs"]];
    initExprs = DeleteDuplicates[initExprsRaw //. simp];
    evolution = tokenEventEvolve[initExprs, indexedRules, simp, accept, steps, OptionValue["MaxStates"]];
    allExprs = evolution["allExprs"];
    trips = evolution["trips"];
    proof = tokenEventProofPath[initExprs, allExprs, trips];
    path = proof["path"];
    pathTrips = proof["pathTrips"];
    redEdges = Flatten[
        Map[
            {DirectedEdge[{"MWState", #[[1]]}, {"MWEv", #}], DirectedEdge[{"MWEv", #}, {"MWState", #[[3]]}]}&,
            pathTrips
        ]
    ];
    pathAxVs = DeleteDuplicates[Map[tokenEventAxiomVertex[#, collapse]&, pathTrips]];
    washAxE = Map[DirectedEdge[tokenEventAxiomVertex[#, collapse], {"MWEv", #}]&, pathTrips];
    evs = Map[{"MWEv", #}&, trips];
    axVs = If[ TrueQ[OptionValue["ShowAxioms"]],
        DeleteDuplicates[Map[tokenEventAxiomVertex[#, collapse]&, trips]]
        ,
        {}
    ];
    verts = Join[Map[{"MWState", #}&, allExprs], evs, axVs];
    edges = Flatten[
        Map[
            Function[tr,
                Join[
                    If[axVs === {}, {}, {DirectedEdge[tokenEventAxiomVertex[tr, collapse], {"MWEv", tr}]}]
                    ,
                    {
                        DirectedEdge[{"MWState", tr[[1]]}, {"MWEv", tr}], DirectedEdge[{"MWEv", tr}, {"MWState", tr[[3]]}]
                    }
                ]
            ]
            ,
            trips
        ]
    ];
    vcols = Join[
        tokenEventStateColors[allExprs, initExprs, path, hl, fadeOp, washOpacity],
        tokenEventEventColors[evs, pathTrips, hl, fadeOp, washOpacity],
        tokenEventAxiomColors[axVs, pathAxVs, hl, fadeOp, washOpacity]
    ];
    vstyles = Map[#[[1]] -> Directive[#[[2, 1]], EdgeForm[#[[2, 2]]]]&, vcols];
    {coords, glayoutOpt} = tokenEventCoordinates[verts, edges, allExprs, initExprs, OptionValue["PinCoords"]];
    Graph[
        verts
        ,
        edges
        ,
        VertexStyle -> vstyles
        ,
        VertexLabels -> None
        ,
        GraphLayout -> glayoutOpt
        ,
        EdgeStyle -> tokenEventEdgeStyles[edges, redEdges, washAxE, hl, asz, fadeOp, washOpacity]
        ,
        VertexCoordinates -> coords
        ,
        If[ TrueQ[OptionValue["Labeled"]],
            VertexShapeFunction -> tokenEventLabeledShapes[allExprs, axVs, evs, initExprs, path, hl, washOpacity, expandedAxioms, collapse]
            ,
            VertexShapeFunction -> tokenEventDiskShapes[verts, vcols, OptionValue["VertexScale"], OptionValue["SizeByLeafCount"]]
        ]
        ,
        PerformanceGoal -> "Quality"
        ,
        ImageSize -> Large
    ]
]

$multiwayPanelOptions = {
    "Steps" -> Automatic,
    "WellFormedOnly" -> True,
    "Labeled" -> False,
    "Oriented" -> Automatic,
    "Ordering" -> Automatic,
    "CriticalPairs" -> Automatic,
    "ArrowSize" -> Automatic,
    "CalloutMaxWidth" -> Automatic,
    "AspectRatio" -> Automatic,
    "Axioms" -> "Proof",
    "Case" -> "Step",
    "Height" -> Automatic,
    "Width" -> Automatic
}

multiwayPanelShow[g_, h_, w_, ar_, defH_, defW_ : None] := Show[
    g
    ,
    ImageSize -> Which[ 
            NumberQ[w],
                w
            ,
            NumberQ[h],
                {Automatic, h}
            ,
            NumberQ[defW],
                defW
            ,
            NumberQ[defH],
                {Automatic, defH}
            ,
            True,
                Automatic
        ]
    ,
    If[NumberQ[ar], AspectRatio -> ar, Unevaluated[Sequence[]]]
]

multiwayPinnedLayeredCoordinates[verts_, edges_, bottomV_, topV_] := Module[{g0, vl, xc, ys, xs, gap, xmid},
    g0 = Graph[verts, edges, GraphLayout -> {"LayeredDigraphEmbedding", "Orientation" -> Bottom}];
    vl = VertexList[g0];
    xc = AssociationThread[vl -> GraphEmbedding[g0]];
    ys = Values[xc][[All, 2]];
    xs = Values[xc][[All, 1]];
    gap = Max[1., (Max[ys] - Min[ys]) / Max[1., Length[Union[Round[ys, 0.5]]] - 1.]];
    xmid = Mean[MinMax[xs]];
    If[bottomV =!= None && KeyExistsQ[xc, bottomV], xc[bottomV] = {xmid, Min[ys] - gap}];
    If[topV =!= None && KeyExistsQ[xc, topV], xc[topV] = {xmid, Max[ys] + gap}];
    Normal[xc]
]

Options[IslandsPanel] = $multiwayPanelOptions

IslandsPanel[ru_, case_String : "Step", OptionsPattern[]] := Module[{s = multiwaySystemFor[ru], base, axs, seeds, steps, cp, g},
    base = If[OptionValue["Axioms"] === "Raw", s["RawAxioms"], s["Axioms"]];
    {axs, seeds, steps, cp} = Switch[ case,
        "Base",
            {base, s["BaseSeeds"], 3, False}
        ,
        "Step",
            {Join[base, s["IH"]], s["StepSeeds"], 4, False}
        ,
        "StepRows",
            {Join[base, s["IH"], s["Rows"]], s["StepSeeds"], 3, False}
        ,
        "CP",
            {Join[base, s["IH"]], s["StepSeeds"], 3, True}
    ];
    If[IntegerQ[OptionValue["Steps"]], steps = OptionValue["Steps"]];
    If[BooleanQ[OptionValue["CriticalPairs"]], cp = OptionValue["CriticalPairs"]];
    g = MultiwayEquationalGraph[
        axs
        ,
        seeds
        ,
        steps
        ,
        "CriticalPairs" -> cp
        ,
        "WellFormedOnly" -> OptionValue["WellFormedOnly"]
        ,
        "Oriented" -> (OptionValue["Oriented"] /. Automatic -> False)
        ,
        "Ordering" -> (OptionValue["Ordering"] /. Automatic -> "LeafCount")
        ,
        "CalloutMaxWidth" -> (OptionValue["CalloutMaxWidth"] /. Automatic -> 240)
        ,
        "VertexLabels" -> If[TrueQ[OptionValue["Labeled"]], True, None]
        ,
        "ArrowSize" -> (
            OptionValue["ArrowSize"]
            /.
            Automatic -> If[NumberQ[OptionValue["Height"]] && OptionValue["Height"] < 280, 0.028, Automatic]
        )
    ];
    multiwayPanelShow[g, OptionValue["Height"], OptionValue["Width"], OptionValue["AspectRatio"], None]
]

Options[StatementPanel] = Join[$multiwayPanelOptions, {"Seeds" -> "Equation"}]

StatementPanel[ru_, k_, OptionsPattern[]] := Module[{s = multiwaySystemFor[ru], base, kk, lab, two, caseB, or, seeds, g},
    lab = TrueQ[OptionValue["Labeled"]];
    two = OptionValue["Seeds"] === "Pair";
    caseB = OptionValue["Case"] === "Base";
    or = OptionValue["Oriented"] /. Automatic -> False;
    base = If[OptionValue["Axioms"] === "Raw", s["RawAxioms"], s["Axioms"]];
    kk = Min[k, Length[s["Rows"]]];
    seeds = If[ caseB,
        If[two, s["BaseSeeds"], {s["BaseSeeds"][[1]] == s["BaseSeeds"][[2]]}]
        ,
        If[two, s["StepSeeds"], {s["StepEq"]}]
    ];
    g = MultiwayGeodesicGraph[
        Join[base, If[caseB, {}, s["IH"]], Take[s["Rows"], kk]],
        seeds,
        OptionValue["Steps"] /. Automatic -> 4,
        "WellFormedOnly" -> OptionValue["WellFormedOnly"],
        "Oriented" -> or,
        "Ordering" -> (OptionValue["Ordering"] /. Automatic -> "LeafCount"),
        "CriticalPairs" -> (OptionValue["CriticalPairs"] /. Automatic -> False),
        "CloudUndirected" -> ! two && ! or,
        "VertexLabels" -> If[lab, True, None],
        "CalloutMaxWidth" -> (OptionValue["CalloutMaxWidth"] /. Automatic -> 170),
        "ArrowSize" -> (OptionValue["ArrowSize"] /. Automatic -> If[lab, Automatic, {0.034, 0.02}])
    ];
    multiwayPanelShow[g, OptionValue["Height"], OptionValue["Width"], OptionValue["AspectRatio"], If[lab, 420, 230]]
]

Options[TokenEventPanel] = Join[
    $multiwayPanelOptions
    ,
    {
        "Seeds" -> "Equation",
        "CollapseAxioms" -> False,
        "ShowAxioms" -> True,
        "SizeByLeafCount" -> False,
        "ProvidedAxioms" -> All,
        "HighlightStyle" -> "Red",
        "WashOpacity" -> 0.5,
        "FadeOpacity" -> 0.13,
        "PinProof" -> False,
        "ProofLayout" -> "LayeredDigraphEmbedding",
        "MaxStates" -> Infinity,
        "VertexScale" -> 1,
        "Root" -> Top,
        "Layout" -> Automatic
    }
]

TokenEventPanel[ru_, k_, OptionsPattern[]] := Module[{s = multiwaySystemFor[ru], base, provided, pa, kk, caseB, seeds, g, pinco},
    caseB = OptionValue["Case"] === "Base";
    base = If[OptionValue["Axioms"] === "Raw", s["RawAxioms"], s["Axioms"]];
    kk = Min[k, Length[s["Rows"]]];
    provided = Join[base, If[caseB, {}, s["IH"]]];
    pa = OptionValue["ProvidedAxioms"] /. All -> Length[provided];
    seeds = If[ OptionValue["Seeds"] === "Pair",
        If[caseB, s["BaseSeeds"], s["StepSeeds"]]
        ,
        If[caseB, {s["BaseSeeds"][[1]] == s["BaseSeeds"][[2]]}, {s["StepEq"]}]
    ];
    pinco = If[ TrueQ[OptionValue["PinProof"]] && ! caseB,
        Module[{p = cachedProofFor[ru], pgc},
            pgc = Normal[z3LayoutCoords[inductionProofGraph[p], "Unlabelled"]];
            Cases[
                pgc,
                (v_ -> c_) /; ListQ[v] && Length[v] == 2 && MatchQ[v[[2]], _HoldForm] :> (ReleaseHold[v[[2]]] -> c)
            ]
        ]
        ,
        {}
    ];
    g = MultiwayTokenEventGraph[
        Join[Take[provided, Min[pa, Length[provided]]], Take[s["Rows"], kk]],
        seeds,
        OptionValue["Steps"] /. Automatic -> 4,
        "Labeled" -> OptionValue["Labeled"],
        "WellFormedOnly" -> OptionValue["WellFormedOnly"],
        "Oriented" -> (OptionValue["Oriented"] /. Automatic -> False),
        "Ordering" -> (OptionValue["Ordering"] /. Automatic -> "LeafCount"),
        "CriticalPairs" -> (OptionValue["CriticalPairs"] /. Automatic -> False),
        "ArrowSize" -> (OptionValue["ArrowSize"] /. Automatic -> 0.011),
        "CollapseAxioms" -> OptionValue["CollapseAxioms"],
        "ShowAxioms" -> OptionValue["ShowAxioms"],
        "SizeByLeafCount" -> OptionValue["SizeByLeafCount"],
        "HighlightStyle" -> OptionValue["HighlightStyle"],
        "VertexScale" -> OptionValue["VertexScale"],
        "WashOpacity" -> OptionValue["WashOpacity"],
        "FadeOpacity" -> OptionValue["FadeOpacity"],
        "PinProof" -> OptionValue["PinProof"],
        "ProofLayout" -> OptionValue["ProofLayout"],
        "PinCoords" -> pinco,
        "MaxStates" -> OptionValue["MaxStates"]
    ];
    multiwayPanelShow[
        Which[ 
            EdgeCount[g] === 0,
                g
            ,
            TrueQ[OptionValue["PinProof"]],
                g
            ,
            OptionValue["Layout"] =!= Automatic,
                Graph[g, GraphLayout -> OptionValue["Layout"], VertexCoordinates -> Automatic]
            ,
            True,
                LayeredGraphPlot[g, OptionValue["Root"]]
        ]
        ,
        OptionValue["Height"]
        ,
        OptionValue["Width"]
        ,
        OptionValue["AspectRatio"]
        ,
        None
        ,
        900
    ]
]

Options[MultiwayBothPanel] = {
    "BaseSteps" -> 6,
    "StepSteps" -> 8,
    "Axioms" -> "Raw",
    "WellFormedOnly" -> False,
    "Oriented" -> False,
    "FadeOpacity" -> 0.15,
    "MaxStates" -> 80,
    "Height" -> 340
}

MultiwayBothPanel[ru_, OptionsPattern[]] := Module[{s = multiwaySystemFor[ru], baseAx, stepAx, cone, gB, gS},
    baseAx = If[OptionValue["Axioms"] === "Raw", s["RawAxioms"], s["Axioms"]];
    stepAx = Join[baseAx, s["IH"], s["Rows"]];
    cone[ax_, seed_, steps_] := Show[
        MultiwayTokenEventGraph[
            ax,
            {seed},
            steps,
            "HighlightStyle" -> "Fade",
            "WellFormedOnly" -> OptionValue["WellFormedOnly"],
            "Oriented" -> OptionValue["Oriented"],
            "FadeOpacity" -> OptionValue["FadeOpacity"],
            "MaxStates" -> OptionValue["MaxStates"]
        ]
        ,
        ImageSize -> {Automatic, OptionValue["Height"]}
    ];
    gB = cone[baseAx, s["BaseSeeds"][[1]] == s["BaseSeeds"][[2]], OptionValue["BaseSteps"]];
    gS = cone[stepAx, s["StepEq"], OptionValue["StepSteps"]];
    Column[
        {
            Row[
                {
                    Labeled[gB, Subscript["P", 0], Top],
                    Spacer[40],
                    Labeled[gS, Row[{Subscript["P", "m"], "  ", Subscript["P", "m+1"]}], Top]
                }
            ]
            ,
            Spacer[12]
            ,
            $inductionRuleCaption
        }
        ,
        Alignment -> Center
        ,
        Spacings -> 1.5
    ]
]

canonicalEquation[e_] := If[ MatchQ[e, _Equal],
    Sort[{canonicalizeVariables[e], canonicalizeVariables[e[[2]] == e[[1]]]}][[1]]
    ,
    canonicalizeVariables[e]
]

inductionProofGraph::usage = "inductionProofGraph[p] builds the token-event proof graph (fused base and step cases) for an inductive proof object p.\nOptions:\n\"GraftDerived\" (True): graft each derived-axiom proof onto its use-site – equational ProofObject chains and inductive sub-proofs; False shows derived axioms as given (green) axioms.\n\"MergeAsAxiom\" (False): colour grafted use-sites as axioms rather than derived theorems.\n\"LemmaComponents\" (All): which lemma case components to include."

Options[inductionProofGraph] = {"GraftDerived" -> True, "MergeAsAxiom" -> False, "LemmaComponents" -> All}

SyntaxInformation[inductionProofGraph] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}

inductionProofGraph[p_, opts : OptionsPattern[]] := Module[
    {records, mergeAsAxiom = TrueQ[OptionValue["MergeAsAxiom"]], lemmaProofs, g, inductiveLemmas}
    ,
    records = fepProofRecords[p];
    If[! AssociationQ[records], Return[$Failed]];
    lemmaProofs = Lookup[p, "LemmaProofs", <||>];
    g = fepGraphFromRecords[records];
    If[ TrueQ[OptionValue["GraftDerived"]],
        g = Fold[graftLemma[#1, #2, mergeAsAxiom]&, g, Cases[Values[lemmaProofs], _ProofObject]];
        inductiveLemmas = Select[Normal[lemmaProofs], AssociationQ[Last[#]] && TrueQ[Last[#]["Valid"]]&];
        g = Fold[
            graftInductiveLemma[#1, ToString[First[#2]], Last[#2], records, mergeAsAxiom, OptionValue["LemmaComponents"]]&,
            g,
            inductiveLemmas
        ]
    ];
    g
]

proofStatementMap[pg_, cl_] := Association[
    Cases[
        VertexList[pg],
        v : {cl, _} /; MatchQ[v[[2]], _HoldForm] :> (canonicalEquation[ReleaseHold[v[[2]]]] -> v)
    ]
]

proofStatementEquations[pg_, cl_] := Cases[VertexList[pg], {cl, h_} /; MatchQ[h, _HoldForm] :> ReleaseHold[h]]

leanCloud[
    ax_,
    seeds_List,
    maxStates_,
    beam_,
    sizeBound_ : Infinity,
    oriented_ : True,
    wellFormedOnly_ : False,
    ordering_ : "LeafCount",
    criticalPairs_ : False,
    bandCenter_ : Automatic
] := Module[{rules, canon, nbrs, wt, target, expand, seed0, final},
    rules = multiwayRulesFromAxioms[ax, TrueQ[oriented], ordering, TrueQ[criticalPairs]];
    canon[eq_] := canonicalEquation[eq];
    seed0 = DeleteDuplicates[canon /@ seeds];
(* Band-pass beam: keep the frontier states whose size is CLOSEST to bandCenter (Automatic = the
   seeds'/proof's median size), so growth concentrates AROUND the proof instead of a low-pass
   flood of trivial small terms. sizeBound caps runaway growth; wellFormedOnly drops malformed
   configs; oriented selects downhill-only rewriting; criticalPairs/ordering tune the rewrite
   rule set. *)
    target = Replace[bandCenter, Automatic :> If[seed0 === {}, 0., N[Median[LeafCount /@ seed0]]]];
    wt[eq_] := Abs[LeafCount[eq] - target];
    nbrs[eq_] := If[ ! MatchQ[eq, _Equal],
        {}
        ,
        Module[{l = eq[[1]], r = eq[[2]]},
            Select[
                DeleteDuplicates[Join[(# == r)& /@ multiwayStep[{l}, rules][[1]], (l == #)& /@ multiwayStep[{r}, rules][[1]]]],
                LeafCount[#] <= sizeBound && (! TrueQ[wellFormedOnly] || wellFormedQ[#])&
            ]
        ]
    ];
    expand[state_] := Module[{candidates, newEdges, allFresh},
        candidates = Flatten[
            Map[
                Function[e,
                    Map[{e, canon[#]}&, nbrs[e]]
                ]
                ,
                state["fr"]
            ]
            ,
            1
        ];
        candidates = DeleteCases[candidates, {x_, x_}];
        newEdges = Map[DirectedEdge[{"MWState", #[[1]]}, {"MWState", #[[2]]}]&, candidates];
        allFresh = DeleteDuplicates[Select[Map[Last, candidates], ! KeyExistsQ[state["seen"], #]&]];
        <|
            "seen" -> Join[state["seen"], AssociationThread[allFresh -> True]],
            "edges" -> Join[state["edges"], AssociationThread[newEdges -> True]],
            "fr" -> Take[SortBy[allFresh, wt], UpTo[beam]]
        |>
    ];
    final = NestWhile[
        expand,
        <|"seen" -> AssociationThread[seed0 -> True], "edges" -> <||>, "fr" -> seed0|>,
        #["fr"] =!= {} && Length[#["seen"]] < maxStates&
    ];
    {{"MWState", #}& /@ Keys[final["seen"]], Keys[final["edges"]]}
]

equationalProofGraph[
    ax_,
    goalEq_,
    steps_,
    gens_,
    maxStates_,
    extraSeeds_ : {},
    beam_ : 60,
    maxNew_ : 40,
    sizeBound_ : Infinity,
    oriented_ : True,
    wellFormedOnly_ : False,
    ordering_ : "LeafCount",
    criticalPairs_ : False,
    bandCenter_ : Automatic
] := Module[{
    lcV,
    lcE,
    teEvent,
    lcV2,
    lcE2,
    rg,
    relabel,
    rgV,
    rgE,
    axNodes,
    canonRule,
    allV,
    allE,
    overSize,
    keep
},
    {lcV, lcE} = leanCloud[
        ax,
        Select[DeleteDuplicates[Join[{goalEq}, extraSeeds]], MatchQ[#, _Equal]&],
        maxStates,
        beam,
        sizeBound,
        oriented,
        wellFormedOnly,
        ordering,
        criticalPairs,
        bandCenter
    ];
(* Token-event form: put an event vertex on every rewrite edge, so the cloud is state -> event -> state (the multiway token-event representation that inductionProofGraph and the other
   multiway graphs use) rather than a bare state graph. The event is keyed by its canonical
   (before, after) pair so equal rewrites merge. *)
    teEvent[e_] := {"MWEv", {canonicalEquation[e[[1, 2]]], canonicalEquation[e[[2, 2]]]}};
    lcE2 = Flatten[
        Map[
            Function[e,
                With[{ev = teEvent[e]},
                    {DirectedEdge[e[[1]], ev], DirectedEdge[ev, e[[2]]]}
                ]
            ]
            ,
            lcE
        ]
    ];
    lcV2 = Join[lcV, DeleteDuplicates[teEvent /@ lcE]];
    rg = MultiwayRuleGraph[
        ax,
        "Generations" -> gens,
        "Oriented" -> TrueQ[oriented],
        "MaxNew" -> maxNew,
        "WellFormedOnly" -> TrueQ[wellFormedOnly],
        "Ordering" -> ordering
    ];
    relabel[v_] := v /. {{"MWRuleV", c_} :> {"MWState", c[[1]] == c[[2]]}, {"MWOv", c_} :> {"MWEv", {"Sup", c}}};
    rgV = relabel /@ VertexList[rg];
    rgE = EdgeList[rg] /. DirectedEdge[a_, b_] :> DirectedEdge[relabel[a], relabel[b]];
    axNodes = {"MWState", forAllBody[#]}& /@ ax;
    canonRule = {"MWState", e_} :> {"MWState", canonicalEquation[e]};
    allV = DeleteDuplicates[Join[lcV2, rgV, axNodes] /. canonRule];
    allE = DeleteCases[DeleteDuplicates[Join[lcE2, rgE] /. canonRule], DirectedEdge[zz_, zz_]];
(* hold the whole cone (rule graph + axiom nodes too, not just the beam cloud) to the size regime,
   so the superposition contribution cannot reintroduce runaway terms *)
    overSize = Association[(# -> True)& /@ Select[allV, MatchQ[#, {"MWState", e_} /; LeafCount[e] > sizeBound]&]];
    keep[v_] := ! KeyExistsQ[overSize, v];
    {Select[allV, keep], Select[allE, keep[First[#]] && keep[Last[#]]&]}
]

Options[multiwaySubProofCones] = {
    "Axioms" -> "Raw",
    "MaxStates" -> 500,
    "SuperposeGenerations" -> 2,
    "Beam" -> 60,
    "MaxNew" -> 40,
    "ThickenAroundProof" -> True,
    "GraftDerived" -> True,
    "SizeBound" -> Automatic,
    "SizeMargin" -> 6,
    "Oriented" -> True,
    "WellFormedOnly" -> False,
    "Ordering" -> "LeafCount",
    "CriticalPairs" -> False,
    "BandCenter" -> Automatic,
    "ProofVertexScale" -> 1,
    "ProofEdgeThickness" -> 1,
    "InductionEdgeThickness" -> 1
}

multiwaySubProofCones[ru_, OptionsPattern[]] := Module[{s = multiwaySystemFor[ru], p = cachedProofFor[ru], pg, baseAx, stepAx, mkCone, caseList},
    pg = inductionProofGraph[p, "GraftDerived" -> OptionValue["GraftDerived"]];
    baseAx = If[OptionValue["Axioms"] === "Raw", s["RawAxioms"], s["Axioms"]];
    stepAx = Join[baseAx, s["IH"], s["Rows"]];
    mkCone[ax_, seed_, cl_] := Module[{extra, seedSet, bound},
        extra = If[TrueQ[OptionValue["ThickenAroundProof"]], proofStatementEquations[pg, cl], {}];
        seedSet = Select[DeleteDuplicates[Join[{seed}, extra]], MatchQ[#, _Equal]&];
(* Automatic size bound = the largest seed term plus a margin of rewrite shells, derived per case
   so each cone is held to its own proof's term-size regime *)
        bound = Replace[
            OptionValue["SizeBound"],
            Automatic :> If[seedSet === {}, Infinity, Max[LeafCount /@ seedSet] + OptionValue["SizeMargin"]]
        ];
        equationalProofGraph[
            ax,
            seed,
            0,
            OptionValue["SuperposeGenerations"],
            OptionValue["MaxStates"],
            extra,
            OptionValue["Beam"],
            OptionValue["MaxNew"],
            bound,
            OptionValue["Oriented"],
            OptionValue["WellFormedOnly"],
            OptionValue["Ordering"],
            OptionValue["CriticalPairs"],
            OptionValue["BandCenter"]
        ]
    ];
    caseList = Join[
        {
            {baseAx, s["BaseSeeds"][[1]] == s["BaseSeeds"][[2]], "Base", "B"},
            {stepAx, s["StepEq"], "Step", "S"}
        }
        ,
        If[ TrueQ[OptionValue["GraftDerived"]],
            Flatten[
                Map[
                    Function[nl,
                        With[{nm = ToString[First[nl]], lp = Last[nl]},
                            {
                                {lp["Axioms"], lp["BaseGoal"], nm <> ":Base", nm <> ".B"},
                                {Join[lp["Axioms"], {lp["IH"]}], lp["StepGoal"], nm <> ":Step", nm <> ".S"}
                            }
                        ]
                    ]
                    ,
                    Select[Normal[Lookup[p, "LemmaProofs", <||>]], AssociationQ[Last[#]] && TrueQ[Last[#]["Valid"]]&]
                ]
                ,
                1
            ]
            ,
            {}
        ]
    ];
    <|
        "ProofGraph" -> pg,
        "CaseList" -> caseList,
        "Cones" -> Association[(#[[4]] -> mkCone[#[[1]], #[[2]], #[[3]]])& /@ caseList]
    |>
]

coneTermSet[cone_] := DeleteDuplicates[canonicalEquation /@ Cases[First[cone], {"MWState", e_ /; MatchQ[e, _Equal]} :> e]]

cloudOverlapMeasure[cones_Association] := Module[{tags = Keys[cones], terms, allTerms, incidence, shared, pairs, overlapEdges, overlapGraph},
    terms = coneTermSet /@ cones;
    allTerms = DeleteDuplicates[Flatten[Values[terms]]];
    incidence[t_] := Select[tags, MemberQ[terms[#], t]&];
    shared = Select[Association[(# -> incidence[#])& /@ allTerms], Length[#] >= 2&];
    pairs = Subsets[tags, {2}];
    overlapEdges = Select[Map[# -> Length[Intersection[terms[First[#]], terms[Last[#]]]]&, pairs], Last[#] > 0&];
    overlapGraph = Graph[tags, UndirectedEdge @@@ Keys[overlapEdges]];
    <|
        "Cones" -> Length[tags],
        "ConeTags" -> tags,
        "ConeSizes" -> Map[Length, terms],
        "SharedTermCount" -> Length[shared],
        "SharedTerms" -> shared,
        "SharingMultiplicity" -> KeySort[Counts[Map[Length, Values[shared]]]],
        "MaxSharing" -> If[Length[shared] == 0, 0, Max[Map[Length, Values[shared]]]],
        "PairwiseOverlap" -> Association[overlapEdges],
        "OverlapGraph" -> overlapGraph,
        "Components" -> Length[ConnectedComponents[overlapGraph]],
        "Connected" -> Length[ConnectedComponents[overlapGraph]] == 1
    |>
]

multiwayCloudOverlap::usage = "multiwayCloudOverlap[ru] measures how the per-sub-proof multiway clouds of machine ru share terms directly. Returns an Association with keys Cones, ConeSizes, SharedTermCount, SharedTerms, SharingMultiplicity (terms shared by exactly k cones, k>=3 = beyond pairwise), MaxSharing, PairwiseOverlap, OverlapGraph, Components, Connected. Accepts the multiwaySubProofCones options (\"MaxStates\", \"GraftDerived\", \"SuperposeGenerations\", \"ThickenAroundProof\", \"Axioms\")."

Options[multiwayCloudOverlap] = Options[multiwaySubProofCones]

SyntaxInformation[multiwayCloudOverlap] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}

multiwayCloudOverlap[ru_, opts : OptionsPattern[]] := cloudOverlapMeasure[multiwaySubProofCones[ru, opts]["Cones"]]

(* mirrors the growth-loop options of MultiwayInductiveProofPanel, on whose behalf this helper runs
   (it is handed the panel's option sequence). *)
Options[directOverlapGrow] = Join[
    {"MaxStates" -> 500, "DirectOverlapCap" -> 4000, "DirectOverlapStep" -> 500},
    Options[multiwaySubProofCones]
]

directOverlapGrow[ru_, opts : OptionsPattern[]] := Module[{
    cap = OptionValue["DirectOverlapCap"],
    step = OptionValue["DirectOverlapStep"],
    m = OptionValue["MaxStates"],
    coneOpts = FilterRules[{opts}, Options[multiwaySubProofCones]],
    data,
    measure
},
    data = multiwaySubProofCones[ru, coneOpts];
    measure = cloudOverlapMeasure[data["Cones"]];
    While[
        ! measure["Connected"] && m < cap
        ,
        m = Min[cap, m + step];
        data = multiwaySubProofCones[ru, "MaxStates" -> m, coneOpts];
        measure = cloudOverlapMeasure[data["Cones"]]
    ];
    <|"MaxStates" -> m, "Data" -> data, "Measure" -> measure|>
]

(* Conclusion pin: a deliberate post-layout nudge of just the goal vertex to the bottom centre, for
   callers who want the conclusion anchored. The axioms are kept on the top row not by a Y
   override but by the in-degree-0 source structure the layout itself ranks (see the panel). *)

pinExtremes[coords_, conclusionV_, pinC_] := If[ ! TrueQ[pinC],
    coords
    ,
    Module[{ys = Values[coords][[All, 2]], yMin, xc, pad},
        yMin = Min[ys];
        xc = Mean[MinMax[Values[coords][[All, 1]]]];
        pad = 0.12 Max[Max[ys] - yMin, 1.];
        Association[
            KeyValueMap[
                Function[{k, v},
                    k -> If[k === conclusionV, {xc, yMin - pad}, v]
                ]
                ,
                coords
            ]
        ]
    ]
]

(* The k-core of the cloud within the combined cloud+proof graph (proof vertices always present).
   Iteratively drops every cloud state whose combined undirected degree is below k, which strips
   the tendrils – degree-1 chains from the outer rewrite shells that carry no confluence
   structure and splay outward under any force layout – leaving the dense, branch-and-reconverge
   mesh. Each removed vertex has degree < k <= the rest, so removal never disconnects the
   surviving graph. *)

cloudKCore[cloudVerts_, cloudEdges_, proofVerts_, k_] := If[ ! IntegerQ[k] || k <= 1 || cloudVerts === {},
    cloudVerts
    ,
    Module[{
        proofSet = Association[(# -> True)& /@ proofVerts],
        edgePairs = List @@@ cloudEdges,
        keptA = Association[(# -> True)& /@ cloudVerts],
        present,
        deg,
        low
    },
        present[x_] := TrueQ[keptA[x]] || KeyExistsQ[proofSet, x];
        While[
            True
            ,
            deg = Merge[
                {
                    Counts[Cases[edgePairs, {a_, b_} /; present[a] && present[b] :> a]],
                    Counts[Cases[edgePairs, {a_, b_} /; present[a] && present[b] :> b]]
                }
                ,
                Total
            ];
            low = Select[Keys[keptA], TrueQ[keptA[#]] && Lookup[deg, Key[#], 0] < k&];
            If[low === {}, Break[]];
            Scan[(keptA[#] = False)&, low]
        ];
        Select[cloudVerts, TrueQ[keptA[#]]&]
    ]
]

MultiwayInductiveProofPanel::usage = "MultiwayInductiveProofPanel[ru] draws the grafted inductive proof graph for Turing machine ru at full opacity, embedded inside the fused multiway term-space cloud of all its sub-proofs.\nOptions:\n\"GraftDerived\" (True): graft each derived-axiom proof (equational + inductive) into the proof graph; False shows derived axioms as given.\n\"ProofVertexScale\" (1): size of the embedded proof vertices.\n\"ProofEdgeThickness\" (1): absolute thickness (points) of ordinary proof edges; 0 hides them.\n\"InductionEdgeThickness\" (2.4): absolute thickness (points) of the induction edges; 0 hides them (a true off switch – not a hairline).\n\"CloudVertexScale\" (1): size multiplier for the cloud state/event discs.\n\"CloudEdgeThickness\" (0.4): absolute thickness (points) of the cloud edges; 0 hides them.\n\"ProofEdgeColor\" (Automatic): colour of the non-induction proof edges (Automatic = the default equational colour); the induction edges always stay purple.\n\"BackgroundOpacity\" (0.25): opacity of the faded cloud.\n\"DirectOverlap\" (False): grow \"MaxStates\" until the sub-proof clouds directly share terms (one component); \"DirectOverlapStep\" (500)/\"DirectOverlapCap\" (4000) bound the growth.\n\"MaxStates\" (500), \"SuperposeGenerations\" (2): total cloud-state cap and superposition generation depth.\n\"SizeBound\" (Automatic), \"SizeMargin\" (6): confine the cloud to the proof's term-size regime – the rewrite system is non-terminating, so unbounded growth fills the cloud with ever-larger runaway configurations; a term is kept only if its LeafCount is within the bound. Automatic = the largest seed term of each case plus SizeMargin rewrite-shells, so the cloud is a bounded neighbourhood that envelops the proof rather than sprawling. Raise SizeMargin (or set SizeBound to a number / Infinity) to admit larger terms.\n\"CloudCore\" (2): keep only the k-core of the cloud – iteratively drop states whose degree (counting edges to the proof) is below k, which removes the splaying degree-1/2 tendrils of the outer rewrite shells and leaves the dense confluent mesh that actually envelops the proof. Set to 0 or 1 to show the full cloud including tendrils; raise to 3 for only the densest core.\n\"Beam\" (60): beam-search width – how many lightest terms each frontier keeps expanding (raise to grow the cloud wider).\n\"MaxNew\" (40): max new vertices per superposition generation.\n\"Layout\" (\"SpringElectricalEmbedding\"): cloud layout (e.g. \"LayeredDigraphEmbedding\"). \"PinProof\" (True): pin the proof at its own z3 layout (via \"PinnedVertices\") while the chosen layout arranges the cloud around it; works under any layout that honours pinned vertices. The axioms are kept on the top row not by a coordinate override but because the cloud edges feeding into them are dropped, leaving them in-degree-0 sources the layered layout ranks together (and is free to order within).\n\"PinConclusion\" (False): nudge the proof's conclusion (goal) vertex to the bottom centre after layout.\n\"ArrowSize\" (0.011): arrowhead size, shared by proof and cloud edges (a plot fraction, independent of edge thickness).\n\"Labeled\" (False): draw the embedded proof vertices as labelled equation boxes; default is unlabelled coloured discs (sized by \"ProofVertexScale\").\n\"Width\" (1000): image width."

Options[MultiwayInductiveProofPanel] = {
    "Axioms" -> "Raw",
    "PinProof" -> True,
    "BackgroundOpacity" -> 0.25,
    "MaxStates" -> 500,
    "SuperposeGenerations" -> 2,
    "Beam" -> 60,
    "MaxNew" -> 40,
    "Layout" -> "SpringElectricalEmbedding",
    "ThickenAroundProof" -> True,
    "GraftDerived" -> True,
    "SizeBound" -> Automatic,
    "SizeMargin" -> 6,
    "CloudCore" -> 2,
    "Oriented" -> True,
    "WellFormedOnly" -> False,
    "Ordering" -> "LeafCount",
    "CriticalPairs" -> False,
    "BandCenter" -> Automatic,
    "DirectOverlap" -> False,
    "DirectOverlapCap" -> 4000,
    "DirectOverlapStep" -> 500,
    "ProofVertexScale" -> 1,
    "ProofEdgeThickness" -> 1,
    "InductionEdgeThickness" -> 2.4,
    "CloudVertexScale" -> 1,
    "CloudEdgeThickness" -> 0.4,
    "PinConclusion" -> False,
    "ArrowSize" -> 0.011,
    "Width" -> Automatic,
    "AspectRatio" -> Automatic,
    "Labeled" -> False,
    "ProofEdgeColor" -> Automatic
}

SyntaxInformation[MultiwayInductiveProofPanel] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}

MultiwayInductiveProofPanel[ru_, opts : OptionsPattern[]] := Module[{
    simp,
    coneData,
    cones,
    pg,
    pv,
    pe,
    pcoordA,
    conclusionV,
    seedVs,
    ceq,
    stmtV,
    reU,
    processCase,
    caseList,
    caseResults,
    multiwayEdges,
    bgV,
    allV,
    allE,
    op,
    proofVsf,
    cloudVStyle,
    proofEStyle,
    cloudEStyle,
    axEqSet,
    styleOpts
},
    simp = $emptyRunSimplification;
    op = OptionValue["BackgroundOpacity"];
    ceq = canonicalEquation;
    coneData = If[ TrueQ[OptionValue["DirectOverlap"]],
        directOverlapGrow[ru, FilterRules[{opts}, Options[directOverlapGrow]]]["Data"]
        ,
        multiwaySubProofCones[ru, FilterRules[{opts}, Options[multiwaySubProofCones]]]
    ];
    cones = coneData["Cones"];
    caseList = coneData["CaseList"];
    pg = coneData["ProofGraph"];
    pv = VertexList[pg];
    pe = EdgeList[pg];
    pcoordA = AssociationThread[pv -> GraphEmbedding[pg]];
    conclusionV = SelectFirst[pv, goalNodeQ, None];
(* PinSeeds and the incoming-edge strip treat the AXIOMS as the true sources, not every in-degree-0
   vertex (some of those are statement/reflexivity nodes the user does not want pinned). *)
    seedVs = Select[pv, axiomVertexQ];
    stmtV[cl_] := proofStatementMap[pg, cl];
    reU[cl_, tag_] := With[{sc = stmtV[cl]},
        Function[v,
            Which[ 
                MatchQ[v, {"MWState", _}] && KeyExistsQ[sc, ceq[v[[2]]]],
                    sc[ceq[v[[2]]]]
                ,
                MatchQ[v, {"MWState", _}],
                    {"BG", "St", ceq[v[[2]]]}
                ,
                True,
                    {"BG", tag, v}
            ]
        ]
    ];
    processCase[{cl_, tag_}] := With[{r = reU[cl, tag], cone = cones[tag]},
        {r /@ cone[[1]], cone[[2]] /. DirectedEdge[a_, b_] :> DirectedEdge[r[a], r[b]]}
    ];
    caseResults = Map[processCase[{#[[3]], #[[4]]}]&, caseList];
    multiwayEdges = DeleteCases[DeleteDuplicates[Flatten[caseResults[[All, 2]], 1]], DirectedEdge[x_, x_]];
(* Keep the axioms TRUE sources: drop every directed cloud edge that feeds INTO an axiom seed (a
   cloud state rewriting to an axiom). The axioms then have in-degree 0, so a layered layout
   ranks them on the top row and is free to optimise their order within that row – a real rank
   constraint, not a post-hoc Y override. (These are directed edges; filter on the target.) *)
    With[{seedSet = Association[(# -> True)& /@ seedVs]},
        multiwayEdges = Select[multiwayEdges, ! KeyExistsQ[seedSet, Last[#]]&]
    ];
    bgV = Select[DeleteDuplicates[Flatten[caseResults[[All, 1]], 1]], MatchQ[#, {"BG", _, _}]&];
    bgV = Intersection[bgV, DeleteDuplicates[Flatten[List @@@ multiwayEdges, 1]]];
    bgV = cloudKCore[bgV, multiwayEdges, pv, OptionValue["CloudCore"]];
    With[{keepset = Association[(# -> True)& /@ Join[pv, bgV]]},
        multiwayEdges = Select[multiwayEdges, KeyExistsQ[keepset, First[#]] && KeyExistsQ[keepset, Last[#]]&]
    ];
    allV = DeleteDuplicates[Join[pv, bgV]];
    allE = DeleteDuplicates[Join[pe, multiwayEdges]];
    axEqSet = Association[(ceq[forAllBody[#]] -> True)& /@ DeleteDuplicates[Flatten[caseList[[All, 1]]]]];
(* Style assembly (coordinate-independent), shared by both layout paths. The proof keeps its own
   shapes; the cloud is drawn through the same Inset disc (resize-stable, never elliptical),
   coloured by the shared multiwayStateStyle / eventVertexStyle, faded by Opacity[op]. *)
    proofVsf = If[ TrueQ[OptionValue["Labeled"]],
        graphOption[pg, VertexShapeFunction]
        ,
        proofDiscShapes[pg, OptionValue["ProofVertexScale"]]
    ];
    cloudVStyle = With[{cpx = $cloudVertexPx OptionValue["CloudVertexScale"]},
        Map[
            Function[v,
                Module[{ev = MatchQ[v, {"BG", _, {"MWEv", _}}], fs},
                    fs = styleFillStroke[If[ev, eventVertexStyle["CriticalPairLemma"], multiwayStateStyle[KeyExistsQ[axEqSet, Last[v]]]]];
                    v -> discVertex[Directive[Opacity[op], fs[[1]]], fs[[2]], If[ev, 0.6 cpx, cpx], 0.5]
                ]
            ]
            ,
            bgV
        ]
    ];
(* Proof-edge thickness is ABSOLUTE points: ProofEdgeThickness for ordinary edges,
   InductionEdgeThickness for induction edges (which stay purple). Either at 0 draws NOTHING –
   a true off switch, where AbsoluteThickness[ 0] would still leave a hairline. *)
(* Proof edges via per-edge EdgeStyle (NOT a shape function) so WL's own edge rendering applies –
   under a layered layout that draws smooth curved/routed edges, not the straight polyline a
   custom Arrow[#1] would force. Thickness is absolute points (0 -> Opacity[0], fully hidden);
   induction edges stay purple. *)
    proofEStyle = With[{
        eqCol = OptionValue["ProofEdgeColor"] /. Automatic -> $equationalEdgeColor,
        peT = OptionValue["ProofEdgeThickness"],
        ieT = OptionValue["InductionEdgeThickness"],
        asz = OptionValue["ArrowSize"]
    },
        Map[
            Function[e,
                With[{ind = MemberQ[{"Induction", "IndApp", "IndIn"}, ToString[edgeTag[e]]]},
                    e -> With[{thick = If[ind, ieT, peT]},
                        If[ thick <= 0,
                            Opacity[0]
                            ,
                            Directive[If[ind, $inductionEdgeColor, eqCol], AbsoluteThickness[thick], Arrowheads[asz]]
                        ]
                    ]
                ]
            ]
            ,
            pe
        ]
    ];
    cloudEStyle = With[{cet = OptionValue["CloudEdgeThickness"], asz = OptionValue["ArrowSize"]},
        Map[
            # -> If[ cet <= 0,
                    Opacity[0]
                    ,
                    Directive[Opacity[op], $equationalEdgeColor, AbsoluteThickness[cet], Arrowheads[asz]]
                ]&
            ,
            multiwayEdges
        ]
    ];
    styleOpts = {
        VertexShapeFunction -> Join[proofVsf, cloudVStyle],
        VertexStyle -> graphOption[pg, VertexStyle],
        EdgeStyle -> Join[proofEStyle, cloudEStyle],
        PlotRangePadding -> Scaled[0.05],
        AspectRatio -> OptionValue["AspectRatio"],
        ImageSize -> OptionValue["Width"]
    };
    If[ ! TrueQ[OptionValue["PinProof"]],
(* Native path: the chosen GraphLayout lays everything out, with WL's real edge routing – so
   "Layout" -> "LayeredDigraphEmbedding" behaves exactly like wrapping the result in
   Graph[..., GraphLayout -> "LayeredDigraphEmbedding"], no baked coordinates, no manual
   wrap. *)
        Graph[allV, allE, GraphLayout -> OptionValue["Layout"], styleOpts]
        ,
        (* Pinned path: pin the proof at its own z3 layout, lay the cloud around it, bake coordinates. *)
        Module[{G0, natD, pscaleA, G, coordsAll, rng},
            G0 = Graph[allV, allE, GraphLayout -> "SpringElectricalEmbedding"];
            natD = Max[(#[[2]] - #[[1]]&) /@ (MinMax /@ Transpose[GraphEmbedding[G0]])];
            pscaleA = With[{
                ctr = Mean /@ Transpose[Values[pcoordA]],
                psz = Max[1., Max[(#[[2]] - #[[1]]&) /@ (MinMax /@ Transpose[Values[pcoordA]])]],
                tgt = $proofLayoutScale * natD
            },
                (tgt / psz * (# - ctr)&) /@ pcoordA
            ];
            G = Graph[
                allV,
                allE,
                VertexCoordinates -> KeyValueMap[Rule, KeyTake[pscaleA, allV]],
                GraphLayout -> {OptionValue["Layout"], "PinnedVertices" -> pv}
            ];
            coordsAll = pinExtremes[AssociationThread[VertexList[G] -> GraphEmbedding[G]], conclusionV, OptionValue["PinConclusion"]];
            rng = MinMax /@ Transpose[Values[coordsAll]];
            Graph[
                allV,
                allE,
                VertexCoordinates -> Normal[KeyTake[coordsAll, allV]],
                PlotRange -> rng,
                styleOpts
            ]
        ]
    ]
]

Options[SettingsPanel] = $multiwayPanelOptions

SettingsPanel[ru_, OptionsPattern[]] := Module[{s = multiwaySystemFor[ru], or},
    or = OptionValue["Oriented"] /. Automatic -> False;
    multiwayPanelShow[
        MultiwayGeodesicGraph[
            Join[s["Axioms"], s["IH"], s["Rows"]],
            {s["StepEq"]},
            OptionValue["Steps"] /. Automatic -> 4,
            "WellFormedOnly" -> OptionValue["WellFormedOnly"],
            "CriticalPairs" -> (OptionValue["CriticalPairs"] /. Automatic -> False),
            "Oriented" -> or,
            "Ordering" -> (OptionValue["Ordering"] /. Automatic -> "LeafCount"),
            "CloudUndirected" -> ! or,
            "VertexLabels" -> If[TrueQ[OptionValue["Labeled"]], True, None],
            "CalloutMaxWidth" -> (OptionValue["CalloutMaxWidth"] /. Automatic -> 170),
            "ArrowSize" -> (OptionValue["ArrowSize"] /. Automatic -> {0.034, 0.02})
        ]
        ,
        OptionValue["Height"]
        ,
        OptionValue["Width"]
        ,
        OptionValue["AspectRatio"]
        ,
        200
    ]
]

ruleVariableQ[term_] := MatchQ[term, _Symbol] && StringMatchQ[ToString[term], ("rv" | "cpv") ~~ ___]

unifyTerms[a_, b_, substitution_, variableQ_] := Module[{x = a //. substitution, y = b //. substitution},
    Which[ 
        x === y,
            substitution
        ,
        variableQ[x],
            If[FreeQ[y, x], Append[substitution, x -> y], $Failed]
        ,
        variableQ[y],
            If[FreeQ[x, y], Append[substitution, y -> x], $Failed]
        ,
        ! AtomQ[x] && ! AtomQ[y] && Head[x] === Head[y] && Length[x] === Length[y],
            Fold[
                If[#1 === $Failed, $Failed, unifyTerms[x[[#2]], y[[#2]], #1, variableQ]]&,
                substitution,
                Range[Length[x]]
            ]
        ,
        True,
            $Failed
    ]
]

canonicalRuleEquation[equation_] := Module[{variables, substitution},
    variables = DeleteDuplicates[Cases[equation, _ ? ruleVariableQ, {0, Infinity}]];
    substitution = Thread[variables -> Take[$ruleCanonicalVariables, Length[variables]]];
    Sort[List @@ (equation /. substitution)]
]

ruleToRewrite[{lhs_, rhs_, variables_}] := With[{lhsPattern = lhs /. Map[# -> Pattern[Evaluate[#], _]&, variables]},
    If[MatchQ[lhsPattern, _Pattern], Nothing, lhsPattern :> rhs]
]

axiomToSuperpositionRule[axiom_, index_, weight_] := Module[
    {body = forAllBody[axiom], variables = forAllVariables[axiom], freshVariables, mapping, lhs, rhs}
    ,
    freshVariables = Map[Symbol["rv" <> ToString[index] <> "v" <> ToString[#]]&, Range[Length[variables]]];
    mapping = Thread[variables -> freshVariables];
    {lhs, rhs} = orientByWeight[{body[[1]] /. mapping, body[[2]] /. mapping}, weight];
    {lhs, rhs, freshVariables}
]

renameToCriticalPairVariables[rule_] := With[{mapping = Thread[rule[[3]] -> Map[Symbol["cpv" <> ToString[#]]&, Range[Length[rule[[3]]]]]]},
    {rule[[1]] /. mapping, rule[[2]] /. mapping}
]

equationToFreshRule[equation_, index_, weight_] := Module[{variables, freshVariables, mapping, lhs, rhs},
    variables = DeleteDuplicates[Cases[equation, _Symbol ? (MemberQ[$ruleCanonicalVariables, #]&), {0, Infinity}]];
    freshVariables = Map[Symbol["rv" <> ToString[index] <> "v" <> ToString[#]]&, Range[Length[variables]]];
    mapping = Thread[variables -> freshVariables];
    {lhs, rhs} = orientByWeight[{equation[[1]] /. mapping, equation[[2]] /. mapping}, weight];
    {lhs, rhs, freshVariables}
]

superpositionNormalizer[oriented_, patternRules_] := If[ oriented,
    Function[term,
        Quiet[
            FixedPoint[
                Quiet[ReplaceRepeated[#, patternRules, MaxIterations -> 40]] //. $emptyRunSimplification&, term, 25
            ]
        ]
    ]
    ,
    Function[term,
        term //. $emptyRunSimplification
    ]
]

directedRules[rules_, canonicalIds_, oriented_] := If[ oriented,
    {rules, canonicalIds}
    ,
    {Flatten[Map[{#, {#[[2]], #[[1]], #[[3]]}}&, rules], 1], Flatten[Map[{#, #}&, canonicalIds], 1]}
]

criticalPairEquation[rule1_, renamedRule2_, position_, normalizer_, wellFormedOnly_] := Module[{
    subterm = If[position === {}, rule1[[1]], Extract[rule1[[1]], position]],
    substitution,
    normalizedLeft,
    normalizedRight
},
    If[ruleVariableQ[subterm] || AtomQ[subterm], Return[$Failed]];
    substitution = unifyTerms[subterm, renamedRule2[[1]], {}, ruleVariableQ];
    If[substitution === $Failed, Return[$Failed]];
    normalizedLeft = normalizer[rule1[[2]] //. substitution];
    normalizedRight = normalizer[
        (If[position === {}, renamedRule2[[2]], ReplacePart[rule1[[1]], position -> renamedRule2[[2]]]])
        //.
        substitution
    ];
    If[normalizedLeft === normalizedRight, Return[$Failed]];
    If[ wellFormedOnly && ! (wellFormedQ[normalizedLeft] && wellFormedQ[normalizedRight]),
        Return[$Failed]
    ];
    canonicalRuleEquation[normalizedLeft == normalizedRight]
]

superpositionCandidates[directed_, directedIds_] := Flatten[
    Table[
        If[ directedIds[[i]] === directedIds[[j]],
            {}
            ,
            With[{rule1 = directed[[i]], renamed = renameToCriticalPairVariables[directed[[j]]]},
                Map[
                    {rule1, renamed, #, directedIds[[i]], directedIds[[j]]}&,
                    Position[rule1[[1]], _, {0, Infinity}, Heads -> False]
                ]
            ]
        ]
        ,
        {i, Length[directed]}
        ,
        {j, Length[directed]}
    ]
    ,
    2
]

addCriticalPair[
    accumulated_,
    {rule1_, renamed_, position_, sourceId1_, sourceId2_},
    normalizer_,
    maxNew_,
    wellFormedOnly_,
    weight_,
    baseRuleCount_,
    generation_
] := If[ Length[accumulated["fresh"]] >= maxNew,
    accumulated
    ,
    Module[{equation = criticalPairEquation[rule1, renamed, position, normalizer, wellFormedOnly]},
        If[ equation === $Failed || KeyExistsQ[accumulated["genOf"], equation],
            accumulated
            ,
            <|
                "nodes" -> Append[accumulated["nodes"], equation]
                ,
                "events" -> Append[accumulated["events"], {"MWOv", equation}]
                ,
                "edges" -> Join[
                        accumulated["edges"]
                        ,
                        {
                            DirectedEdge[{"MWRuleV", sourceId1}, {"MWOv", equation}],
                            DirectedEdge[{"MWRuleV", sourceId2}, {"MWOv", equation}],
                            DirectedEdge[{"MWOv", equation}, {"MWRuleV", equation}]
                        }
                    ]
                ,
                "genOf" -> Append[accumulated["genOf"], equation -> generation]
                ,
                "fresh" -> Append[
                        accumulated["fresh"],
                        equationToFreshRule[equation, baseRuleCount + Length[accumulated["fresh"]] + 1, weight]
                    ]
                ,
                "freshIds" -> Append[accumulated["freshIds"], equation]
            |>
        ]
    ]
]

superposeGeneration[state_, generation_, oriented_, maxNew_, wellFormedOnly_, weight_] := Module[{
    rules = state["rules"],
    canonicalIds = state["cid"],
    patternRules,
    normalizer,
    directed,
    directedIds,
    accumulated
},
    patternRules = Map[ruleToRewrite, rules];
    normalizer = superpositionNormalizer[oriented, patternRules];
    {directed, directedIds} = directedRules[rules, canonicalIds, oriented];
    accumulated = Fold[
        addCriticalPair[#1, #2, normalizer, maxNew, wellFormedOnly, weight, Length[rules], generation]&
        ,
        <|
            "nodes" -> state["nodes"],
            "events" -> state["events"],
            "edges" -> state["edges"],
            "genOf" -> state["genOf"],
            "fresh" -> {},
            "freshIds" -> {}
        |>
        ,
        superpositionCandidates[directed, directedIds]
    ];
    <|
        "rules" -> Join[rules, accumulated["fresh"]],
        "cid" -> Join[canonicalIds, accumulated["freshIds"]],
        "nodes" -> accumulated["nodes"],
        "events" -> accumulated["events"],
        "edges" -> accumulated["edges"],
        "genOf" -> accumulated["genOf"]
    |>
]

seedRuleNodes[canonicalIds_] := Fold[
    If[ KeyExistsQ[#1["genOf"], #2],
        #1
        ,
        <|"nodes" -> Append[#1["nodes"], #2], "genOf" -> Append[#1["genOf"], #2 -> 0]|>
    ]&
    ,
    <|"nodes" -> {}, "genOf" -> <||>|>
    ,
    canonicalIds
]

placeRuleLayer[placed_, layer_, edges_, yOf_, dx_] := Module[{barycenterOf, ordered, count},
    barycenterOf[v_] := Mean[Lookup[placed, Map[First, Select[edges, Last[#] === v&]], {0.}][[All, 1]]];
    ordered = SortBy[layer, {barycenterOf[#]&, ToString[#, InputForm]&}];
    count = Length[ordered];
    Join[placed, Association[MapIndexed[#1 -> {(First[#2] - (count + 1) / 2.) dx, yOf[#1]}&, ordered]]]
]

ruleVertexLayout[nodes_, events_, edges_, genOf_, labeled_] := Module[{dx = If[labeled, 4.6, 1.4], generationFloor, yOf, layers},
    generationFloor = Association[
        Map[
            Function[c,
                c -> Min[Append[Cases[edges, DirectedEdge[{"MWRuleV", c}, {"MWOv", cc_}] :> genOf[cc]], 1]]
            ]
            ,
            Select[nodes, genOf[#] === 0&]
        ]
    ];
    yOf[{"MWRuleV", c_}] := If[genOf[c] === 0, -(2 generationFloor[c] - 2), -2 genOf[c]];
    yOf[{"MWOv", c_}] := -(2 genOf[c] - 1);
    layers = SortBy[GatherBy[Join[Map[{"MWRuleV", #}&, nodes], events], yOf], -yOf[First[#]]&];
    Normal[Fold[placeRuleLayer[#1, #2, edges, yOf, dx]&, <||>, layers]]
]

ruleVertexScaleFactor[method_, n_] := Switch[ method,
    "Fixed" | "None",
        1.
    ,
    "Linear",
        100. / Max[100, n]
    ,
    _,
        Sqrt[100. / Max[100, n]]
]

ruleSpaceGraph[state_, labeled_, arrowSize_, scalingMethod_ : "Density", vertexScale_ : 1] := Module[{
    nodes = state["nodes"],
    events = state["events"],
    edges = DeleteDuplicates[state["edges"]],
    genOf = state["genOf"],
    coords,
    scale
},
    coords = ruleVertexLayout[nodes, events, edges, genOf, labeled];
    scale = vertexScale ruleVertexScaleFactor[scalingMethod, Length[nodes] + Length[events]];
    Graph[
        Join[Map[{"MWRuleV", #}&, nodes], events]
        ,
        edges
        ,
        VertexStyle -> Join[
                Map[{"MWRuleV", #} -> multiwayStateStyle[genOf[#] === 0]&, nodes],
                Map[# -> eventVertexStyle["CriticalPairLemma"]&, events]
            ]
        ,
        If[ labeled,
            VertexShapeFunction -> Join[
                Map[
                    Function[c,
                        {"MWRuleV", c} -> equationVertexShape[renderGraphEquation[HoldForm @@ {c[[1]] == c[[2]]}], genOf[c] === 0, 3]
                    ]
                    ,
                    nodes
                ]
                ,
                Map[# -> eventVertexShape[8, "CriticalPairLemma"]&, events]
            ]
            ,
            VertexSize -> Join[Map[{"MWRuleV", #} -> {"Scaled", 0.018 scale}&, nodes], Map[# -> {"Scaled", 0.008 scale}&, events]]
        ]
        ,
        VertexLabels -> None
        ,
        EdgeStyle -> Directive[$equationalEdgeColor, Arrowheads[arrowSize]]
        ,
        VertexCoordinates -> coords
        ,
        PerformanceGoal -> "Quality"
        ,
        ImageSize -> Large
    ]
]

MultiwayRuleGraph::usage = "MultiwayRuleGraph[axioms] builds the superposition (critical-pair) rule-space graph of an equational axiom set.\nOptions:\n\"Generations\" (1), \"MaxNew\" (25): superposition depth and max new rules per generation.\n\"VertexScaling\" (\"Density\"): how unlabelled vertex size adapts to the node count – \"Density\" (gentle 1/Sqrt shrink), \"Linear\" (faster 1/n shrink), or \"Fixed\" (constant).\n\"VertexScale\" (1): multiplier on the unlabelled vertex sizes (lower to shrink large graphs).\n\"Oriented\" (True), \"Ordering\" (\"RunUnfold\"), \"Labeled\" (False), \"WellFormedOnly\" (False), \"ArrowSize\" (0.011)."

Options[MultiwayRuleGraph] = {
    "Generations" -> 1,
    "MaxNew" -> 25,
    "Oriented" -> True,
    "Ordering" -> "RunUnfold",
    "Labeled" -> False,
    "WellFormedOnly" -> False,
    "ArrowSize" -> 0.011,
    "VertexScaling" -> "Density",
    "VertexScale" -> 1
}

SyntaxInformation[MultiwayRuleGraph] = {"ArgumentsPattern" -> {_, OptionsPattern[]}}

MultiwayRuleGraph[axioms_List, OptionsPattern[]] := Module[{
    weight = If[OptionValue["Ordering"] === "LeafCount", LeafCount, runUnfoldWeight],
    rules,
    canonicalIds,
    seeded,
    finalState
},
    rules = Select[MapIndexed[axiomToSuperpositionRule[#1, First[#2], weight]&, axioms], ! MatchQ[#[[1]], _Symbol]&];
    canonicalIds = Map[canonicalRuleEquation[#[[1]] == #[[2]]]&, rules];
    seeded = seedRuleNodes[canonicalIds];
    finalState = Fold[
        superposeGeneration[
            #1,
            #2,
            TrueQ[OptionValue["Oriented"]],
            OptionValue["MaxNew"],
            TrueQ[OptionValue["WellFormedOnly"]],
            weight
        ]&
        ,
        <|
            "rules" -> rules,
            "cid" -> canonicalIds,
            "nodes" -> seeded["nodes"],
            "events" -> {},
            "edges" -> {},
            "genOf" -> seeded["genOf"]
        |>
        ,
        Range[OptionValue["Generations"]]
    ];
    ruleSpaceGraph[
        finalState,
        TrueQ[OptionValue["Labeled"]],
        OptionValue["ArrowSize"],
        OptionValue["VertexScaling"],
        OptionValue["VertexScale"]
    ]
]

Options[RuleSpacePanel] = Join[$multiwayPanelOptions, {"Generations" -> 1, "MaxNew" -> 25}]

RuleSpacePanel[ru_, OptionsPattern[]] := Module[{s = multiwaySystemFor[ru]},
    multiwayPanelShow[
        MultiwayRuleGraph[
            Join[s["Axioms"], s["IH"]],
            "Generations" -> OptionValue["Generations"],
            "Oriented" -> (OptionValue["Oriented"] /. Automatic -> True),
            "Ordering" -> (OptionValue["Ordering"] /. Automatic -> "RunUnfold"),
            "MaxNew" -> OptionValue["MaxNew"],
            "WellFormedOnly" -> OptionValue["WellFormedOnly"],
            "Labeled" -> OptionValue["Labeled"],
            "ArrowSize" -> (OptionValue["ArrowSize"] /. Automatic -> 0.011)
        ]
        ,
        OptionValue["Height"]
        ,
        OptionValue["Width"]
        ,
        OptionValue["AspectRatio"]
        ,
        None
        ,
        1300
    ]
]

(* === Z3 layered layout engine === *)

(* Modular pipeline; geometry is decided by positions, never by bending edges: conclusions sit at
   balanced offsets so their straight edges read 135/45, and the induction hypothesis descends
   the induction node's empty gap column to enter from above at 90. Every edge is a single
   straight segment clipped to box borders; the one exception is the hypothesis edge (<=3
   segments). Boxes are sized in COORDINATE units and drawn at that size under uniform aspect,
   so the non-overlap margin is a true box-edge margin. Layouts are cached on disk keyed by
   graph structure + box sizes. *)

$spineForkWeight = 6; $axiomWeight = 2; $indWeight = 9; $goalWeight = 7; $channelPull = 3

(* a non-induction fan-in (>=2 parents) gets ONE parent, the one with the deepest chain above it,
   pulled straight onto the child, so the spine runs straight and the others branch in; a
   symmetric pull (spineFork) only straddles them. Induction nodes keep their symmetric Y. *)

$primaryAlignWeight = 40

$ihAlignWeight = 60; (* IHAboveCircle: strength of the soft pull of the hyp column onto the induction node's x *)

(* crossing minimisation: weight on each crossing indicator in the Z3 objective, and the cap on how
   many candidate crossing pairs are encoded (the weighted MaxSAT stops returning a model past a
   few hundred; ~200 is the tractable sweet spot, ~7s, and takes 1512 from 20 -> 11). *)

$crossMinWeight = 100; $crossMinPairCap = 200

(* bump whenever the layout algorithm changes (not just its style inputs), so cachedLayoutFor
   invalidates every stored layoutcache_*.mx instead of serving a layout from the old code. *)

$z3LayoutVersion = 8

(* layout works in PRINTER'S POINTS: box size = real BoundingBox in points, the same unit as
   ImageSize, so fixed-size Inset boxes (no size argument, stable under cell resize) never
   overlap. Disc/gap values below are also points. *)

$edgeMargin = 8; $dummyWidth = 4; $edgeOvershoot = 3

$eventDiam = 11; $indDiam = 17; $circleDiam = 16; $indCircleDiam = 24; $cloudVertexPx = 5

$layerGapLabelled = 22; $layerGapUnlabelled = 10

(* opt-in proofGraph layout knobs (default = no change). $conclusionGap adds vertical length (pts)
   below the induction circle so its edge to the conclusion vertex is longer; affects
   coordinates so it is in the layout-cache key. $roundRouting renders any routed
   (multi-waypoint) edge – the IH trunk – as a smooth spline instead of straight segments;
   render-only, so it is in z3StyleKey. $axiomRows drops each axiom onto its target event's row
   so the axiom->event edge runs horizontally. $ihAboveCircle pulls the routed IH (hyp) column
   hard onto the induction node's x, so the purple edge descends straight into the circle and
   nonov clears boxes off that column (the box itself stays where the layering puts it, so the
   step spine is not dragged). $axiomGap (Automatic = one ranksep) sets the horizontal distance
   from an axiom box to the event circle it feeds. These reshape the layout, so they go in both
   the layout-cache and style keys. *)

$conclusionGap = 0; $roundRouting = False; $axiomRows = False; $ihAboveCircle = False; $axiomGap = Automatic

$axiomSide = "Left"; (* AxiomSide: which side of its event circle an axiom box sits on ("Left"/"Right") *)

gv[a_, k_] := Lookup[a, Key[k]]

z3ColorOf[g_] := Association[
    Map[
        #[[1]] -> FirstCase[#[[2]], _Hue | _RGBColor | _GrayLevel | _LightDarkSwitched, $InductiveProofColors["FallbackFrame"], Infinity]&,
        graphOption[g, VertexStyle]
    ]
]

(* the induction-hypothesis vertices are filled with $inductionFill; z3RoleOf detects the "hyp"
   role by this colour, so it must equal $inductionFill, not a copy of it *)
$indHypColor = $inductionFill

z3AxiomColorQ[c_] := MatchQ[c, (Hue[h_, _, _] | LightDarkSwitched[Hue[h_, _, _], _]) /; h < 0.4]

z3RoleOf[v_, colA_] := Which[ 
    eventVertexQ[v],
        "event"
    ,
    inductionNodeQ[v],
        "ind"
    ,
    goalNodeQ[v],
        "goal"
    ,
    z3AxiomColorQ[gv[colA, v]],
        "axiom"
    ,
    gv[colA, v] === $indHypColor,
        "hyp"
    ,
    True,
        "stmt"
]

z3ClusterTag[v_] := If[ListQ[v] && Length[v] >= 1, ToString[v[[1]]], ""]

z3Prefix[t_] := If[StringContainsQ[t, ":"], First[StringSplit[t, ":"]], ""]

z3SuffixRank[t_] := Which[ 
    StringContainsQ[t, "Base"],
        0
    ,
    StringContainsQ[t, "Step"],
        2
    ,
    True,
        1
]

z3LabelledSizes[g_] := Module[{boxR, sa},
    boxR = Select[
        graphOption[g, VertexShapeFunction],
        ListQ[#[[1]]] && ! eventVertexQ[#[[1]]] && ! inductionNodeQ[#[[1]]]&
    ];
    sa = Association[Map[#[[1]] -> boxBBox[First[#[[2]][Null]]]&, boxR]];
    Join[
        sa
        ,
        Association[
            Map[
                # -> Which[ 
                        eventVertexQ[#],
                            {$eventDiam, $eventDiam}
                        ,
                        inductionNodeQ[#],
                            {$indDiam, $indDiam}
                        ,
                        True,
                            {$eventDiam, $eventDiam}
                    ]&
                ,
                Select[VertexList[g], ! KeyExistsQ[sa, #]&]
            ]
        ]
    ]
]

z3UnlabelledSizes[g_] := Association[
    Map[
        # -> $vertexScale If[inductionNodeQ[#], {$indCircleDiam, $indCircleDiam}, {$circleDiam, $circleDiam}]&
        ,
        VertexList[g]
    ]
]

z3LayerAssign[g_, idx_] := Module[{n = VertexCount[g], pairs, L, ch = True, p = 0},
    pairs = Map[{idx[#[[1]]], idx[#[[2]]]}&, EdgeList[g]];
    L = ConstantArray[0, n];
    While[
        ch && p < n + 2
        ,
        ch = False;
        p++;
        Do[
            If[ L[[e[[1]]]] < L[[e[[2]]]] + 1,
                L[[e[[1]]]] = L[[e[[2]]]] + 1;
                ch = True
            ]
            ,
            {e, pairs}
        ]
    ];
    L
]

z3Info[g_, sizeA_, ranksep_] := Module[{vs, ed, idx, colA, ctag, prefixes, role, layer, outA},
    vs = VertexList[g];
    ed = EdgeList[g];
    idx = AssociationThread[vs -> Range[Length[vs]]];
    colA = z3ColorOf[g];
    ctag = AssociationMap[z3ClusterTag, vs];
    prefixes = DeleteDuplicates[z3Prefix /@ Values[ctag]];
    role = AssociationMap[z3RoleOf[#, colA]&, vs];
    layer = AssociationThread[vs -> z3LayerAssign[g, idx]];
    outA = Merge[Map[#[[1]] -> #[[2]]&, ed], Identity];
(* AxiomRows: drop each axiom-like given (axiom OR identity theorem) onto its target event's row,
   so the edge into the event runs horizontally (same y) instead of diagonally from the row
   above. *)
    If[ TrueQ[$axiomRows],
        Scan[
            Function[ax,
                With[{ev = SelectFirst[Lookup[outA, Key[ax], {}], eventVertexQ, None]},
                    If[ev =!= None, layer[ax] = layer[ev]]
                ]
            ]
            ,
            Select[vs, axiomLikeQ]
        ]
    ];
(* IHAboveCircle pulls the hyp box onto the induction node's x (soft constraint in z3Constraints),
   so the whole purple column is vertical /directly above the circle. Its row is left as the
   longest-path layering assigns it, so the routed hyp edge stays well-formed. *)
    <|
        "g" -> g
        ,
        "vs" -> vs
        ,
        "ed" -> ed
        ,
        "idx" -> idx
        ,
        "sizes" -> sizeA
        ,
        "ranksep" -> ranksep
        ,
        "role" -> role
        ,
        "cluster" -> AssociationMap[(3 (First[FirstPosition[prefixes, z3Prefix[gv[ctag, #]]]] - 1) + z3SuffixRank[gv[ctag, #]])&, vs]
        ,
        "in" -> Merge[Map[#[[2]] -> #[[1]]&, ed], Identity]
        ,
        "out" -> outA
        ,
        "layer" -> layer
    |>
]

z3In[info_, v_] := Lookup[info["in"], Key[v], {}]

z3Out[info_, v_] := Lookup[info["out"], Key[v], {}]

z3MainSubject[info_, e_] := Module[{subj},
    subj = Select[z3In[info, e], MatchQ[gv[info["role"], #], "stmt" | "hyp"]&];
    If[subj === {}, None, First[SortBy[subj, {-Boole[z3In[info, #] =!= {}], -gv[info["layer"], #]}&]]]
]

z3Trunk[info_] := Module[{trunk = <||>, walk},
    walk[v_] := If[ ! KeyExistsQ[trunk, Key[v]],
        trunk[v] = True;
        Module[{ev = SelectFirst[z3In[info, v], eventVertexQ, None]},
            If[ ev =!= None,
                trunk[ev] = True;
                With[{main = z3MainSubject[info, ev]},
                    If[main =!= None, walk[main]]
                ]
            ]
        ]
    ];
    Scan[walk, Select[info["ed"], inductionNodeQ[#[[2]]] && gv[info["role"], #[[1]]] =!= "hyp"&][[All, 1]]];
    trunk
]

z3HypRoutes[info_] := Module[{idx = info["idx"], layer = info["layer"], role = info["role"]},
    Association[
        Map[
            Function[e,
                e -> Join[
                    {e[[1]]},
                    {"dum", idx[e[[1]]], idx[e[[2]]], #}& /@ Range[gv[layer, e[[1]]] - 1, gv[layer, e[[2]]] + 1, -1],
                    {e[[2]]}
                ]
            ]
            ,
            Select[info["ed"], gv[role, #[[1]]] === "hyp" && gv[layer, #[[1]]] - gv[layer, #[[2]]] >= 2&]
        ]
    ]
]

z3NodeData[info_, routes_] := Module[{vs = info["vs"], dummies, nodes, isDummy},
    isDummy[nd_] := MatchQ[nd, {"dum", __}];
    dummies = DeleteDuplicates[Select[Flatten[Values[routes], 1], isDummy]];
    nodes = Join[vs, dummies];
    <|
        "nodes" -> nodes
        ,
        "layer" -> Association[Map[# -> If[isDummy[#], Last[#], gv[info["layer"], #]]&, nodes]]
        ,
        "width" -> Association[Map[# -> If[isDummy[#], $dummyWidth, gv[info["sizes"], #][[1]]]&, nodes]]
        ,
        "cluster" -> Association[Map[# -> gv[info["cluster"], If[isDummy[#], vs[[#[[3]]]], #]]&, nodes]]
        ,
        "class" -> Association[
                Map[
                    # -> Which[ 
                            isDummy[#],
                                2
                            ,
                            KeyExistsQ[info["trunk"], Key[#]],
                                2
                            ,
                            True,
                                0
                        ]&
                    ,
                    nodes
                ]
            ]
        ,
        "idx" -> AssociationThread[nodes -> Range[Length[nodes]]]
    |>
]

z3OrderSweep[nd_, nbrs_, passes_ : 6] := Module[{nodes = nd["nodes"], layerF, clusterF, classF, idxF, layers, ordL, posOf},
    layerF[x_] := gv[nd["layer"], x];
    clusterF[x_] := gv[nd["cluster"], x];
    classF[x_] := gv[nd["class"], x];
    idxF[x_] := gv[nd["idx"], x];
    layers = Sort[DeleteDuplicates[layerF /@ nodes]];
    ordL = Map[SortBy[#, {clusterF[#]&, classF[#]&, idxF[#]&}]&, GroupBy[nodes, layerF]];
    posOf = Association[
        Flatten[
            KeyValueMap[
                Function[{L, lst},
                    MapIndexed[#1 -> #2[[1]]&, lst]
                ]
                ,
                ordL
            ]
        ]
    ];
    Do[
        Module[{dir = If[OddQ[pass], -1, 1], sweepLs},
            sweepLs = If[OddQ[pass], layers, Reverse[layers]];
            Do[
                With[{ref = L + dir},
                    ordL[L] = SortBy[
                        ordL[L]
                        ,
                        Function[x,
                            {
                                clusterF[x]
                                ,
                                classF[x]
                                ,
                                With[{ns = Select[Lookup[nbrs, Key[x], {}], layerF[#] == ref&]},
                                    If[ns === {}, gv[posOf, x], Mean[N[gv[posOf, #]& /@ ns]]]
                                ]
                                ,
                                idxF[x]
                            }
                        ]
                    ];
                    Do[posOf[ordL[L][[k]]] = k, {k, Length[ordL[L]]}]
                ]
                ,
                {L, sweepLs}
            ]
        ]
        ,
        {pass, passes}
    ];
    posOf
]

z3NodeAdjacency[info_, routes_] := Merge[
    Flatten[
        Map[
            Function[e,
                Map[
                    {#[[1]] -> #[[2]], #[[2]] -> #[[1]]}&,
                    If[KeyExistsQ[routes, e], Partition[routes[e], 2, 1], {{e[[1]], e[[2]]}}]
                ]
            ]
            ,
            info["ed"]
        ]
        ,
        2
    ]
    ,
    Identity
]

z3EventCons[info_, xOf_, e_] := Module[{rs = info["ranksep"], outs, main, sides, hard, soft},
    outs = z3Out[info, e];
    main = z3MainSubject[info, e];
    sides = DeleteCases[z3In[info, e], main];
    hard = Map[If[Length[z3In[info, #]] == 1, xOf[e] == xOf[#], Nothing]&, outs];
    soft = Map[If[Length[z3In[info, #]] == 1, Nothing, {$spineForkWeight, xOf[e] - xOf[#]}]&, outs];
(* the event sits under its main subject. Normally a hard equality, but under IHAboveCircle the
   main subject of an event IS the IH/hyp box – hard-pinning it to the event would freeze the
   box to the step spine and stop it moving over the induction circle, so make that tie soft. *)
    If[ main =!= None,
        If[ Length[Select[z3Out[info, main], eventVertexQ]] == 1
        &&
        ! (TrueQ[$ihAboveCircle] && gv[info["role"], main] === "hyp"),
            hard = Append[hard, xOf[main] == xOf[e]]
            ,
            soft = Append[soft, {$spineForkWeight, xOf[main] - xOf[e]}]
        ]
    ];
(* axiom (side) inputs sit one ranksep to the left of the event circle by default; AxiomSide
   "Right" puts them to the right instead (the z3OrderSweep order is flipped to match in
   z3Layout). *)
    soft = Join[
        soft,
        Map[{$axiomWeight, If[$axiomSide === "Right", xOf[#] - xOf[e], xOf[e] - xOf[#]] - rs}&, sides]
    ];
    {hard, soft}
]

z3IndCons[info_, xOf_, ind_] := Module[{rs = info["ranksep"], entries, k, offs, goalV, soft},
    entries = SortBy[
        Select[info["ed"], #[[2]] === ind && gv[info["role"], #[[1]]] =!= "hyp"&][[All, 1]],
        gv[info["cluster"], #]&
    ];
    k = Length[entries];
    offs = Which[ 
        k == 0,
            {}
        ,
        k == 1,
            {0}
        ,
        True,
            Table[rs (-1 + 2 (j - 1) / (k - 1)), {j, k}]
    ];
    soft = MapThread[{$indWeight, xOf[#1] - xOf[ind] - #2}&, {entries, offs}];
    goalV = SelectFirst[z3Out[info, ind], goalNodeQ, None];
    If[goalV =!= None, Append[soft, {$goalWeight, xOf[goalV] - xOf[ind]}], soft]
]

z3Constraints[info_, nd_, routes_, posOf_, xv_] := Module[{
    xOf,
    nodes = nd["nodes"],
    byLayer,
    nonov,
    channelHard,
    channelPull,
    ev,
    indCons,
    fanInAlign,
    ihCol,
    hard,
    soft
},
    xOf[x_] := xv[[gv[nd["idx"], x]]];
    byLayer = GroupBy[nodes, gv[nd["layer"], #]&];
(* per-layer non-overlap. AxiomGap (when set) widens the edge-to-edge margin between an axiom box
   and the event circle it sits next to (this hard floor, not a soft pull, is what actually
   sets the distance – the Sugiyama order pins the relative x, so a soft cannot move it). *)
    nonov = Flatten[
        Map[
            Function[grp,
                With[{o = SortBy[grp, gv[posOf, #]&]},
                    MapThread[
                        xOf[#2] - xOf[#1] >=
                            (gv[nd["width"], #1] + gv[nd["width"], #2]) / 2 +
                                If[ (axiomLikeQ[#1] && eventVertexQ[#2]) || (eventVertexQ[#1] && axiomLikeQ[#2]),
                                    Replace[$axiomGap, Automatic :> $edgeMargin]
                                    ,
                                    $edgeMargin
                                ]&
                        ,
                        {Most[o], Rest[o]}
                    ]
                ]
            ]
            ,
            Values[byLayer]
        ]
        ,
        1
    ];
    channelHard = Flatten[
        Map[
            Function[e,
                With[{ch = routes[e]},
                    Table[xOf[ch[[k]]] == xOf[ch[[k + 1]]], {k, 2, Length[ch] - 2}]
                ]
            ]
            ,
            Keys[routes]
        ]
        ,
        1
    ];
    channelPull = Flatten[
        Map[
            Function[e,
                With[{ch = routes[e], tgt = routes[e][[-1]]},
                    Map[{$channelPull, xOf[#] - xOf[tgt]}&, ch[[2 ;; -2]]]
                ]
            ]
            ,
            Keys[routes]
        ]
        ,
        1
    ];
    ev = Map[z3EventCons[info, xOf, #]&, Select[info["vs"], gv[info["role"], #] === "event"&]];
    indCons = Map[z3IndCons[info, xOf, #]&, Select[info["vs"], inductionNodeQ]];
    fanInAlign = If[ $primaryAlignWeight == 0,
        {}
        ,
        DeleteCases[
            Map[
                Function[c,
                    With[{ps = Lookup[info["in"], Key[c], {}]},
                        If[ Length[ps] >= 2 && ! inductionNodeQ[c],
                            {$primaryAlignWeight, xOf[First[MaximalBy[ps, Length[VertexInComponent[info["g"], #]]&]]] - xOf[c]}
                            ,
                            Null
                        ]
                    ]
                ]
                ,
                info["vs"]
            ]
            ,
            Null
        ]
    ];
(* IHAboveCircle: align the purple hypothesis vertex above the induction circle. Two soft pulls,
   both onto the induction node's x: the hyp BOX itself (so the framed vertex sits above the
   circle) and every routed waypoint of the hyp COLUMN (so the purple edge descends straight
   into the circle); nonov then pushes other boxes off that column. Soft, not hard – a hard
   x-equality collides with boxes already pinned to the column and makes the solve infeasible. *)
    ihCol = If[ ! TrueQ[$ihAboveCircle],
        {}
        ,
        With[{
            ih = SelectFirst[info["vs"], gv[info["role"], #] === "hyp"&, None],
            ind = SelectFirst[info["vs"], inductionNodeQ, None]
        },
            Join[
                If[ih =!= None && ind =!= None, {{$ihAlignWeight, xOf[ih] - xOf[ind]}}, {}]
                ,
                Flatten[
                    Map[
                        Function[e,
                            With[{ch = routes[e], tgt = routes[e][[-1]]},
                                Map[{$ihAlignWeight, xOf[#] - xOf[tgt]}&, ch[[2 ;; -2]]]
                            ]
                        ]
                        ,
                        Keys[routes]
                    ]
                    ,
                    1
                ]
            ]
        ]
    ];
    hard = Join[nonov, channelHard, Flatten[ev[[All, 1]], 1]];
    soft = Join[channelPull, Flatten[ev[[All, 2]], 1], Flatten[indCons, 1], fanInAlign, ihCol];
    <|"hard" -> hard, "soft" -> soft|>
]

z3SolveX[cons_, nd_] := Module[{nodes = nd["nodes"], xv, av, soft = cons["soft"], auxCons, obj, m},
    ensureZ3Link[];
    xv = Table[WolframInstitute`Z3Link`Z3Real["x" <> ToString[k]], {k, Length[nodes]}];
    av = Table[WolframInstitute`Z3Link`Z3Real["a" <> ToString[k]], {k, Length[soft]}];
    auxCons = Flatten[MapThread[{#2 >= #1[[2]], #2 >= -#1[[2]]}&, {soft, av}], 1];
    obj = Total[MapThread[#1[[1]] #2&, {soft, av}]];
    m = WolframInstitute`Z3Link`Z3Optimize[obj -> Minimize, Join[cons["hard"], auxCons, {xv[[1]] == 0}]]["Model"];
    AssociationThread[nodes -> Table[N[Lookup[m, "x" <> ToString[k], 0]], {k, Length[nodes]}]]
]

z3Border[c_, half_, circleQ_, towards_, push_ : $edgeOvershoot] := Module[{d = towards - c, sx, sy, b},
    If[Norm[d] < 10. ^ -9, Return[c]];
    b = If[ circleQ,
        c + Min[half] Normalize[d]
        ,
        sx = If[Abs[d[[1]]] < 10. ^ -9, Infinity, half[[1]] / Abs[d[[1]]]];
        sy = If[Abs[d[[2]]] < 10. ^ -9, Infinity, half[[2]] / Abs[d[[2]]]];
        c + Min[sx, sy] d
    ];
    b - push Normalize[d] (* push > 0 reaches into the box, < 0 stops clear of it, extending a little into the box so the line reaches it *)
]

(* raw routes (waypoints at vertex centres). Endpoint clipping to the box/circle borders is done at
   render time in z3Graphic, so the arrow gaps are render params, not layout-cache keys. *)

z3EdgeRoutes[info_, nd_, routes_, allX_] := Module[{rs = info["ranksep"], posR},
    posR[x_] := {gv[allX, x], gv[nd["layer"], x] rs - If[goalNodeQ[x], $conclusionGap, 0]};
    Association[
        Map[
            Function[e,
                e -> If[KeyExistsQ[routes, e], z3Simplify[Map[posR, routes[e]]], {posR[e[[1]]], posR[e[[2]]]}]
            ]
            ,
            info["ed"]
        ]
    ]
]

z3Simplify[pts_] := Module[{kept},
    kept = Select[
        Range[2, Length[pts] - 1]
        ,
        Abs[
                (pts[[#]][[1]] - pts[[# - 1]][[1]]) (pts[[# + 1]][[2]] - pts[[# - 1]][[2]])
                -
                (pts[[#]][[2]] - pts[[# - 1]][[2]]) (pts[[# + 1]][[1]] - pts[[# - 1]][[1]])
            ] > 10. ^ -6&
    ];
    Join[{First[pts]}, pts[[kept]], {Last[pts]}]
]

(* number of edge crossings in a solved layout (coordinate polylines). Segments that share a vertex
   coordinate are not counted (the orientation test rejects the touching endpoint). *)

z3SegCross[{a_, b_}, {c_, d_}] := Module[{o, d1, d2, d3, d4},
    o[p_, q_, r_] := Sign[(q[[1]] - p[[1]]) (r[[2]] - p[[2]]) - (q[[2]] - p[[2]]) (r[[1]] - p[[1]])];
    d1 = o[c, d, a];
    d2 = o[c, d, b];
    d3 = o[a, b, c];
    d4 = o[a, b, d];
    d1 != d2 && d3 != d4 && d1 != 0 && d2 != 0 && d3 != 0 && d4 != 0
]

z3CrossCount[rc_] := Module[{es = Values[rc], sg},
    sg[p_] := Partition[p, 2, 1];
    Sum[
        If[AnyTrue[Tuples[{sg[es[[i]]], sg[es[[j]]]}], Quiet @ TrueQ @ z3SegCross[#[[1]], #[[2]]]&], 1, 0],
        {i, Length[es]},
        {j, i + 1, Length[es]}
    ]
]

(* crossing indicators for the Z3 objective. Each segment goes monotonically down the layers, so
   two segments cross iff their relative horizontal order flips between the top and bottom of
   their shared layer range. The order at a level is x-interpolated (linear in the node x's), so
   crossing = Xor of two comparison booleans -> Boole[..] is a 0/1 term to minimise. Capped at
   $crossMinPairCap candidate pairs (the weighted MaxSAT stops returning a model past a few
   100). *)

z3CrossingTerms[info_, nd_, routes_, xv_, ranksep_, capN_] := Module[{layerY, xOf, xAtY, segsOfEdge, allSegs, yr, cand, terms},
    ensureZ3Link[];
    layerY[v_] := gv[nd["layer"], v] ranksep;
    xOf[v_] := xv[[gv[nd["idx"], v]]];
    xAtY[{a_, b_}, y_] := With[{y1 = layerY[a], y2 = layerY[b]},
        xOf[a] + (xOf[b] - xOf[a]) (y1 - y) / (y1 - y2)
    ];
    segsOfEdge[e_] := Partition[If[KeyExistsQ[routes, e], routes[e], {e[[1]], e[[2]]}], 2, 1];
    allSegs = Flatten[Map[segsOfEdge, info["ed"]], 1];
    yr[s_] := MinMax[layerY /@ s];
    cand = Take[
        Select[
            Subsets[allSegs, {2}]
            ,
            (Min[yr[#[[1]]][[2]], yr[#[[2]]][[2]]] - Max[yr[#[[1]]][[1]], yr[#[[2]]][[1]]]) > 0.01
            &&
            ! IntersectingQ[#[[1]], #[[2]]]&
        ]
        ,
        UpTo[capN]
    ];
    terms = MapIndexed[
        Function[{p, idx},
            Module[{s1 = p[[1]], s2 = p[[2]], yLo, yHi, sh, sl, ci = First[idx] - 1},
                yLo = Max[yr[s1][[1]], yr[s2][[1]]];
                yHi = Min[yr[s1][[2]], yr[s2][[2]]];
                sh = WolframInstitute`Z3Link`Z3Bool["sh" <> ToString[ci]];
                sl = WolframInstitute`Z3Link`Z3Bool["sl" <> ToString[ci]];
                {
                    {Equivalent[sh, xAtY[s1, yHi] >= xAtY[s2, yHi]], Equivalent[sl, xAtY[s1, yLo] >= xAtY[s2, yLo]]},
                    Boole[Xor[sh, sl]]
                }
            ]
        ]
        ,
        cand
    ];
    {Flatten[terms[[All, 1]]], terms[[All, 2]]}
]

z3SolveXCross[cons_, crossCons_, crossTerms_, nd_, xv_] := Module[{nodes = nd["nodes"], av, auxCons, obj, m},
    ensureZ3Link[];
    av = Table[WolframInstitute`Z3Link`Z3Real["a" <> ToString[k]], {k, Length[cons["soft"]]}];
    auxCons = Flatten[MapThread[{#2 >= #1[[2]], #2 >= -#1[[2]]}&, {cons["soft"], av}], 1];
    obj = Total[MapThread[#1[[1]] #2&, {cons["soft"], av}]] + $crossMinWeight Total[crossTerms];
    m = Quiet
    @
    WolframInstitute`Z3Link`Z3Optimize[obj -> Minimize, Join[cons["hard"], auxCons, crossCons, {xv[[1]] == 0}]]["Model"];
    If[ AssociationQ[m],
        AssociationThread[nodes -> Table[N[Lookup[m, "x" <> ToString[k], 0]], {k, Length[nodes]}]]
        ,
        $Failed
    ]
]

z3Layout[g_, sizeA_, ranksep_] := Module[{info, routes, nd, posOf, xv, cons, allX, baseCross, cc, ct, allX2},
    ensureZ3Link[];
    info = z3Info[g, sizeA, ranksep];
    info = Append[info, "trunk" -> z3Trunk[info]];
    routes = z3HypRoutes[info];
    nd = z3NodeData[info, routes];
    posOf = z3OrderSweep[nd, z3NodeAdjacency[info, routes]];
(* AxiomSide "Right": reorder each axiom box to just after its event on the shared row, so the
   left-to-right order (and hence nonov) puts it to the right of the circle it feeds. *)
    If[ $axiomSide === "Right",
        Scan[
            Function[ax,
                With[{ev = SelectFirst[Lookup[info["out"], Key[ax], {}], eventVertexQ, None]},
                    If[ev =!= None && gv[info["layer"], ax] === gv[info["layer"], ev], posOf[ax] = gv[posOf, ev] + 0.5]
                ]
            ]
            ,
            Select[info["vs"], axiomLikeQ]
        ]
    ];
    xv = Table[WolframInstitute`Z3Link`Z3Real["x" <> ToString[k]], {k, Length[nd["nodes"]]}];
    cons = z3Constraints[info, nd, routes, posOf, xv];
    allX = z3SolveX[cons, nd];
    baseCross = z3CrossCount[z3EdgeRoutes[info, nd, routes, allX]];
(* crossing minimisation runs only when the baseline has crossings, so a 0-crossing layout (453,
   445) is byte-identical; the result is kept only if it strictly improves, never a
   regression, and falls back to the baseline if the MaxSAT returns no model. *)
    If[ baseCross > 0,
        {cc, ct} = z3CrossingTerms[info, nd, routes, xv, ranksep, $crossMinPairCap];
        allX2 = z3SolveXCross[cons, cc, ct, nd, xv];
        If[ allX2 =!= $Failed && z3CrossCount[z3EdgeRoutes[info, nd, routes, allX2]] < baseCross,
            allX = allX2
        ]
    ];
    <|
        "coords" -> AssociationThread[
            info["vs"] -> Map[{gv[allX, #], gv[info["layer"], #] ranksep - If[goalNodeQ[#], $conclusionGap, 0]}&, info["vs"]]
        ]
        ,
        "routes" -> z3EdgeRoutes[info, nd, routes, allX]
    |>
]

(* layout cache: disk + memo, keyed by graph structure + size knobs + mode. Box sizes are measured
   only on a miss; the result stores them so a hit skips measuring too. *)

z3Ranksep[sizeA_, mode_] := Max[Values[sizeA][[All, 2]]] + If[mode === "Unlabelled", $layerGapUnlabelled, $layerGapLabelled]

z3SizesFor[g_, mode_] := If[mode === "Unlabelled", z3UnlabelledSizes[g], z3LabelledSizes[g]]

$z3LayoutMemo = <||>

cachedLayoutFor[g_, mode_] := Module[{key, f, lay},
    key = Hash[{
        VertexList[g], EdgeList[g],
        $graphCellSize, $cellFontScale, $quantifierSize, $textFontSize, $boxPadding,
        $traditionalForm, $quantifierTraditional, $scriptRaise, $centerOnEquals,
        $vertexScale, $cellSeparatorGap, $z3LayoutVersion, mode,
        (* every parameter that changes the solved layout, so a weight change re-keys (and is
           cached separately) instead of silently serving an old layout or clobbering a sibling *)
        $spineForkWeight, $axiomWeight, $indWeight, $goalWeight, $channelPull,
        $primaryAlignWeight, $crossMinWeight, $crossMinPairCap,
        $layerGapLabelled, $layerGapUnlabelled, $edgeMargin, $dummyWidth, $conclusionGap,
        $axiomRows, $ihAboveCircle, $axiomGap, $axiomSide
    }];
    If[KeyExistsQ[$z3LayoutMemo, key], Return[$z3LayoutMemo[key]]];
    f = FileNameJoin[{$proofCacheDir, "layoutcache_" <> ToString[key] <> ".mx"}];
    lay = If[ FileExistsQ[f],
        Import[f]
        ,
        Module[{sizeA = z3SizesFor[g, mode]},
            With[
                {l = Append[z3Layout[g, sizeA, z3Ranksep[sizeA, mode]], "sizes" -> sizeA]}
                ,
(* only persist a layout whose coordinates are all real numbers; a failed Z3 solve leaves
   unevaluated Lookup[Missing,..] coords, and caching that would poison every later
   call *)
                If[AllTrue[Values[l["coords"]], VectorQ[#, NumberQ]&], Export[f, l]];
                l
            ]
        ]
    ];
    $z3LayoutMemo[key] = lay;
    lay
]

z3LayoutCoords[g_, mode_] := cachedLayoutFor[g, mode]["coords"]

(* the fill+stroke of a vertex as the Labelled rendering draws it: a box vertex's Framed Background
   + FrameStyle colour, an event/induction disc's own fill+stroke. Shared by the z3Graphic
   Unlabelled discs and the multiway panel so colours match across every rendering. *)

z3FillStroke[funcA_, colA_, v_] := If[ ListQ[v] && ! eventVertexQ[v] && ! inductionNodeQ[v],
    With[{fr = First[Lookup[funcA, Key[v]][Null]]},
        {
            FirstCase[fr, HoldPattern[Background -> b_] :> b, gv[colA, v], Infinity],
            FirstCase[fr, HoldPattern[FrameStyle -> Directive[c_, ___]] :> c, $InductiveProofColors["FallbackFrame"], Infinity]
        }
    ]
    ,
    {gv[colA, v], If[inductionNodeQ[v], $inductionStroke, $InductiveProofColors["FallbackFrame"]]}
]

(* Unlabelled-style disc shapes for a proof graph, for embedding the proof unlabelled in the
   multiway panel; colours match the Labelled boxes via z3FillStroke. scale is ProofVertexScale. *)

proofDiscShapes[g_, scale_] := With[{colA = z3ColorOf[g], funcA = Association[graphOption[g, VertexShapeFunction]]},
    Map[
        Function[v,
            With[{fs = z3FillStroke[funcA, colA, v]},
                v -> discVertex[
                        fs[[1]],
                        fs[[2]],
                        scale (If[inductionNodeQ[v], $indCircleDiam, $circleDiam]),
                        If[inductionNodeQ[v], 1.4, 0.8]
                    ]
            ]
        ]
        ,
        VertexList[g]
    ]
]

z3VertexShape[v_, mode_, sz_, fill_, stroke_, content_] := Which[ 
    inductionNodeQ[v],
        discVertex[fill, stroke, sz[[1]], 1.4]
    ,
    mode === "Unlabelled" || eventVertexQ[v],
        discVertex[fill, stroke, sz[[1]], 0.8]
    ,
    True,
        With[{im = content},
            (Inset[im, #1]&)
        ]
]

z3Graphic[g_, mode_] := Module[
    {lay, sizeA, coords, routes, colA, funcA, contentOf, clipEnd, circleQ, vsf, esf, exts, xr, yr}
    ,
    lay = cachedLayoutFor[g, mode];
    coords = lay["coords"];
    routes = lay["routes"];
    sizeA = lay["sizes"];
    colA = z3ColorOf[g];
    funcA = Association[graphOption[g, VertexShapeFunction]];
(* draw the Framed box at its natural point size (Inset with no size argument): it equals the
   BoundingBox the layout reserved, never rescales with the cell, never reflows *)
    contentOf[v_] := First[Lookup[funcA, Key[v]][Null]];
(* the Unlabelled disc reuses the EXACT fill and stroke of the Labelled rendering (z3FillStroke) so
   the two modes are colour-identical for every vertex. *)
    vsf = Map[
        Function[v,
            With[{fs = z3FillStroke[funcA, colA, v]},
                v -> z3VertexShape[
                        v,
                        mode,
                        gv[sizeA, v],
                        fs[[1]],
                        fs[[2]],
                        If[mode === "Unlabelled" || eventVertexQ[v] || inductionNodeQ[v], None, contentOf[v]]
                    ]
            ]
        ]
        ,
        VertexList[g]
    ];
    (* clip each end to its vertex border; the gap into a circle and into a box are separate *)
    circleQ[v_] := eventVertexQ[v] || inductionNodeQ[v];
    clipEnd[v_, towards_, push_] := z3Border[gv[coords, v], gv[sizeA, v] / 2, circleQ[v], towards, push];
    esf = KeyValueMap[
        Function[{e, p},
            e -> Module[{pp = p, st = edgeStyleFor[edgeTag[e]], ah, src, tgt},
                src = clipEnd[e[[1]], pp[[2]], $edgeOvershoot];
                tgt = clipEnd[e[[2]], pp[[-2]], -If[circleQ[e[[2]]], $circleArrowGap, $boxArrowGap]];
                pp[[1]] = src;
                pp[[-1]] = tgt;
                ah = arrowheadsFor[FirstCase[st, AbsoluteThickness[t_] :> t, 0.8, Infinity]];
(* a routed edge (> 2 waypoints) is rounded to a smooth spline when $roundRouting is on; decide
   here (inside the render Block) since the edge function is applied later, outside it *)
                With[{drawPts = If[TrueQ[$roundRouting] && Length[pp] > 2, BSplineCurve[pp], pp]},
                    ({st, ah, Arrow[drawPts]}&)
                ]
            ]
        ]
        ,
        routes
    ];
    exts = Join[
        KeyValueMap[{#2[[1]] + {-1, 1} gv[sizeA, #1][[1]] / 2, #2[[2]] + {-1, 1} gv[sizeA, #1][[2]] / 2}&, coords],
        Map[{{#[[1]], #[[1]]}, {#[[2]], #[[2]]}}&, Flatten[Values[routes], 1]]
    ];
    xr = MinMax[exts[[All, 1]]];
    yr = MinMax[exts[[All, 2]]];
    Graph[
        g,
        VertexCoordinates -> Normal[coords],
        VertexShapeFunction -> vsf,
        EdgeShapeFunction -> esf,
        PlotRange -> {xr, yr},
        PlotRangePadding -> 14,
        AspectRatio -> (yr[[2]] - yr[[1]]) / (xr[[2]] - xr[[1]]),
        ImageSize -> (xr[[2]] - xr[[1]])
    ]
]

(* render entry point. Same standard option set as RenderAxiomGrid (via withRenderStyle). Built
   fresh each session and memoised in memory keyed by (machine, mode, resolved style); the
   expensive part, the Z3 layout solve, is what's cached on disk (cachedLayoutFor). *)

$z3GraphicMemo = <||>

z3StyleKey[] := {
    $graphCellSize,
    $cellFontScale,
    $textFontSize,
    $boxPadding,
    $quantifierSize,
    $traditionalForm,
    $quantifierTraditional,
    $scriptRaise,
    $centerOnEquals,
    $arrowSize,
    $arrowScalesWithThickness,
    $vertexScale,
    $boxEdgeThickness,
    $cellEdgeThickness,
    $inductionEdgeThickness,
    $arrowGap,
    $boxArrowGap,
    $circleArrowGap,
    $cellSeparatorGap,
    $dotRadius,
    $quantifierNudge,
    $cellEdgeColor,
    $roundRouting,
    $conclusionGap,
    $axiomRows,
    $ihAboveCircle,
    $axiomGap,
    $axiomSide
}

(* Render the proof graph with a built-in Wolfram layout instead of the Z3 solver: same vertex
   shapes (z3VertexShape boxes/discs) and edge colours (edgeStyleFor) as z3Graphic, but the
   chosen GraphLayout places the vertices and routes the edges. *)

proofGraphWL[g_, mode_, layout_] := Module[{sizeA, colA, funcA, vsf, estyle},
    sizeA = z3SizesFor[g, mode];
    colA = z3ColorOf[g];
    funcA = Association[graphOption[g, VertexShapeFunction]];
    vsf = Map[
        Function[v,
            With[{fs = z3FillStroke[funcA, colA, v]},
                v -> z3VertexShape[
                        v
                        ,
                        mode
                        ,
                        gv[sizeA, v]
                        ,
                        fs[[1]]
                        ,
                        fs[[2]]
                        ,
                        If[ mode === "Unlabelled" || eventVertexQ[v] || inductionNodeQ[v],
                            None
                            ,
                            First[Lookup[funcA, Key[v]][Null]]
                        ]
                    ]
            ]
        ]
        ,
        VertexList[g]
    ];
    estyle = Map[# -> Directive[edgeStyleFor[edgeTag[#]], Arrowheads[$arrowSize]]&, EdgeList[g]];
    Graph[
        VertexList[g],
        EdgeList[g],
        GraphLayout -> layout,
        VertexShapeFunction -> vsf,
        EdgeStyle -> estyle,
        VertexLabels -> None,
        PerformanceGoal -> "Quality"
    ]
]

(* "Layout" (Automatic) selects the renderer: Automatic = the Z3 layout engine (z3Graphic); any
   GraphLayout spec (e.g. "LayeredDigraphEmbedding") = Wolfram's layout via proofGraphWL. *)

Options[proofGraph] = $renderStyleOptions

proofGraph[ru_Integer, mode_String, opts : OptionsPattern[]] := withRenderStyle[
    $graphCellSize
    ,
    {opts}
    ,
    With[{lo = OptionValue["Layout"]},
        If[ lo === Automatic,
            With[{key = Hash[{ru, mode, z3StyleKey[]}]},
                Lookup[
                    $z3GraphicMemo, key, $z3GraphicMemo[key] = z3Graphic[inductionProofGraph[cachedProofFor[ru]], mode]
                ]
            ]
            ,
            proofGraphWL[inductionProofGraph[cachedProofFor[ru]], mode, lo]
        ]
    ]
]

proofGraph[p_ ? AssociationQ, mode_String, opts : OptionsPattern[]] := withRenderStyle[
    $graphCellSize
    ,
    {opts}
    ,
    With[{lo = OptionValue["Layout"]},
        If[ lo === Automatic,
            z3Graphic[inductionProofGraph[p], mode]
            ,
            proofGraphWL[inductionProofGraph[p], mode, lo]
        ]
    ]
]

End[]

EndPackage[]