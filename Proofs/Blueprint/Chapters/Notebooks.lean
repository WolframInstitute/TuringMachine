/-
  Blueprint.Chapters.Notebooks

  Chapter 11 of the blueprint: the computational notebooks in one place: every node that
  has a Wolfram notebook, grouped along the chain, with a link to the node,
  the notebook in the Wolfram Cloud and a button that opens it next to the
  text. The notebooks use the functions of the paclet
  WolframInstitute/TuringMachine; see `Blueprint/Notebook.lean` and
  `scripts/CloudDeployNotebooks.wl`.
-/

import Verso
import VersoManual
import VersoBlueprint
import Blueprint.Notebook

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Blueprint (notebook)

#doc (Manual) "Computational notebooks" =>

%%%
tag := "notebooks"
file := "notebooks"
htmlSplit := .never
%%%

Every node below has a Wolfram notebook that computes its objects on small examples:
the encoders and decoders of the chain, the runs of the systems, and the bounds. The
notebooks use the functions of the paclet
[WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/),
each of which follows the Lean definition named on its reference page. The button
under each entry opens the notebook beside the text, as it does under the node
itself; the other link opens it in the Wolfram Cloud.

# A Turing machine as a tag system

From {ref "tm-to-cts"}[the chapter on the machine reduction].

*The Cocke-Minsky tag system.* {bpref "TagSystem.tagK"}[`TagSystem.tagK`]: A binary Turing machine as a 2-tag system: each configuration is a word spelling its two tape halves in unary, and every machine step is a few rounds of tag steps. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/TagSystem.tagK.nb).

:::notebook "TagSystem.tagK"
:::

*One machine step as tag rounds.* {bpref "TagSystem.tm_step_tag"}[`TagSystem.tm_step_tag`]: Each machine step is three rounds of tag steps for a move to the right and five for a move to the left; at the end of the rounds the tag word is the word of the next configuration. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/TagSystem.tm_step_tag.nb).

:::notebook "TagSystem.tm_step_tag"
:::

*Cook's cyclic tag system.* {bpref "TagSystem.tagToCTS"}[`TagSystem.tagToCTS`]: A 2-tag system over k symbols as a cyclic tag system with 2k appendants: each symbol a block of k bits with a single 1, one appendant per production, then k empty ones. One cycle of the appendants is one tag step. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/TagSystem.tagToCTS.nb).

:::notebook "TagSystem.tagToCTS"
:::

# A cyclic tag system as System 5

From {ref "cts-to-system5"}[the chapter on cyclic tag to System 5].

*Smith's System 5 encoder.* {bpref "BiTM.ctsToSystem5"}[`BiTM.ctsToSystem5`]: A cyclic tag system as a System 5 program: the working string becomes a bag of integers, each appendant four rules, repeated for a number of cycles. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/BiTM.ctsToSystem5.nb).

:::notebook "BiTM.ctsToSystem5"
:::

*The run of System 5.* {bpref "BiTM.System5.step"}[`BiTM.System5.step`]: Every step decrements the bag and increments the rules; an element reaching 0 is removed and the next rule is merged into the bag with parity. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/BiTM.System5.step.nb).

:::notebook "BiTM.System5.step"
:::

*Reading the working string off the bag.* {bpref "Smith.decodeBag"}[`Smith.decodeBag`]: The sorted bag read in pairs: a gap of 1 is a 0, a gap of 2 a 1. Along the System 5 run the decoded strings are the run of the doubled cyclic tag system. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/Smith.decodeBag.nb).

:::notebook "Smith.decodeBag"
:::

# System 5 as System 4

From {ref "system5-to-system4"}[the chapter on System 5 to System 4].

*The System 4 tape of a System 5 program.* {bpref "BiTM.system5ToSystem4"}[`BiTM.system5ToSystem4`]: The bag becomes one set, followed by f star and empty-set pairs and a block of 8f elements for each rule. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/BiTM.system5ToSystem4.nb).

:::notebook "BiTM.system5ToSystem4"
:::

*The run of System 4.* {bpref "BiTM.System4.step"}[`BiTM.System4.step`]: In state A the head moves left, deleting stars; at the left end it turns and sweeps right in states B and C, decrementing every set it passes. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/BiTM.System4.step.nb).

:::notebook "BiTM.System4.step"
:::

*Reading the bag off System 4.* {bpref "Smith.decodeS4"}[`Smith.decodeS4`]: With the parameters of the proof, the leading sets of System 4, each time its head is back at the left end in state B, decode to the System 5 bags in order, then the decrements of a terminal phase. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/Smith.decodeS4.nb).

:::notebook "Smith.decodeS4"
:::

# System 4 as System 3

From {ref "system4-to-system3"}[the chapter on System 4 to System 3].

*Smith's strings for one-element sets.* {bpref "Smith.row"}[`Smith.row`]: The string for the set `{i}` at width `n` is row i of the rule 60 cellular automaton started from 2 1 1 ... 1: cell j is the binomial coefficient C(i, j) mod 2. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/Smith.row.nb).

:::notebook "Smith.row"
:::

*The System 3 tape.* {bpref "Smith.initAC"}[`Smith.initAC`]: Each set of the System 4 tape becomes a block of 2^w cells whose parity scans give the set, each star a 0, with a left end 0^h 2 2 1 and a closing 1. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/Smith.initAC.nb).

:::notebook "Smith.initAC"
:::

# Wolfram's 2,3 machine

From {ref "machine-model"}[the chapter on the machine model].

*Wolfram's 2,3 Turing machine.* {bpref "BiTM.wolfram23"}[`BiTM.wolfram23`]: Two states and three colors: A0 -> 1RB, A1 -> 2LA, A2 -> 1LA, B0 -> 2LA, B1 -> 2RB, B2 -> 0RA. It never halts. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/BiTM.wolfram23.nb).

:::notebook "BiTM.wolfram23"
:::

# Decoding, run bounds and the closed form

From {ref "conjecture0"}[the chapter on Conjecture 0].

*Reading the bag off wolfram23.* {bpref "Smith.decodeW23"}[`Smith.decodeW23`]: At the times the proof schedules, when wolfram23 is back at the left end of its tape in state B, the blocks from the head to the first 0 decode to the bag that System 4 holds at the matching step. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/Smith.decodeW23.nb).

:::notebook "Smith.decodeW23"
:::

*The System 5 run bound.* {bpref "Smith.System5.run_bound"}[`Smith.System5.run_bound`]: A System 5 run from the encoder's output with r rules and integers at most B has at most B 2^r steps. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/Smith.System5.run_bound.nb).

:::notebook "Smith.System5.run_bound"
:::

*The System 4 run bound.* {bpref "Smith.System4.run_bound"}[`Smith.System4.run_bound`]: System 4 always halts: a run from a tape of length L has at most (2L + 2)(L + 1) steps, by a measure that drops at every step. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/Smith.System4.run_bound.nb).

:::notebook "Smith.System4.run_bound"
:::

*The closed-form parameters.* {bpref "Smith.icStart"}[`Smith.icStart`]: The initial condition of the proof takes every run length from a bound, so that it is a definition that runs no system. The bounds are far larger than the runs. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/Smith.icStart.nb).

:::notebook "Smith.icStart"
:::

# The composition

From {ref "universality"}[the chapter on the composition].

*The tag time bound.* {bpref "TagSystem.tagTime_le"}[`TagSystem.tagTime_le`]: n machine steps from a configuration with sz c explicit cells take at most n 15 2^(sz c + n) tag steps. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/TagSystem.tagTime_le.nb).

:::notebook "TagSystem.tagTime_le"
:::

*How large IC is.* {bpref "Smith.IC"}[`Smith.IC`]: The initial condition for n steps of a machine goes through every stage of the chain. The stages up to System 5 can be built; the later ones are far too large and are computed only in size. [Open in the Wolfram Cloud](https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/Smith.IC.nb).

:::notebook "Smith.IC"
:::
