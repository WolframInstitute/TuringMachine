/-
  Blueprint

  The top-level document of the Verso blueprint: the prose companion of the
  Lean proof of Wolfram (2,3) universality, one chapter per link of the
  chain, the formal statements linked to the declarations that carry them,
  the dependency graph and the progress summary. Rendered by
  `lake exe vbp build` (see `BlueprintMain.lean`).
-/

import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Blueprint.Chapters.Overview
import Blueprint.Chapters.MachineModel
import Blueprint.Chapters.TMToCTS
import Blueprint.Chapters.CTSToSystem5
import Blueprint.Chapters.System5ToSystem4
import Blueprint.Chapters.System4ToSystem3
import Blueprint.Chapters.Systems3210
import Blueprint.Chapters.Conjecture0
import Blueprint.Chapters.Universality
import Blueprint.Chapters.InfiniteForm
import Blueprint.Chapters.Notebooks
import Blueprint.Chapters.OpenItems

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Wolfram (2,3) universality in Lean" =>

A machine-checked development of Alex Smith's 2007 proof that Wolfram's 2-state
3-colour Turing machine emulates every two-colour cyclic tag system, extended by
a Cocke-Minsky reduction from binary Turing machines to cyclic tag systems. The
two headline theorems are {bpref "Smith.wolfram23_universal_ic"}[`Smith.wolfram23_universal_ic`] (the finite form: for
every run of `n` steps of a machine, the finite tape `IC tm c n` reproduces it) and
{bpref "Smith.wolfram23_infinite_ic"}[`Smith.wolfram23_infinite_ic`] (the infinite form: one right-infinite tape
`ITape tm c` per machine and input on which the emulation runs for ever). Both
tapes are definitions, computed from the machine and its input by Smith's
encoders and closed-form bounds on the run lengths, without running anything.

Each chapter states the mathematics of one link of the chain in words, links
the statements that carry it to their Lean declarations, and says what is
proved, what is assumed, and what is left out. The reader who wants the
theorems reads the overview; the reader who wants to audit one link reads that
chapter and opens the module it names. Page numbers refer to [Smith's paper](https://www.wolframscience.com/prizes/tm23/TM23Proof.pdf)
(TM23Proof.pdf, his submission for the Wolfram 2,3 Turing machine prize).

{include 0 Blueprint.Chapters.Overview}
{include 0 Blueprint.Chapters.MachineModel}
{include 0 Blueprint.Chapters.TMToCTS}
{include 0 Blueprint.Chapters.CTSToSystem5}
{include 0 Blueprint.Chapters.System5ToSystem4}
{include 0 Blueprint.Chapters.System4ToSystem3}
{include 0 Blueprint.Chapters.Systems3210}
{include 0 Blueprint.Chapters.Conjecture0}
{include 0 Blueprint.Chapters.Universality}
{include 0 Blueprint.Chapters.InfiniteForm}
{include 0 Blueprint.Chapters.Notebooks}
{include 0 Blueprint.Chapters.OpenItems}

{blueprint_graph}
{blueprint_summary}
