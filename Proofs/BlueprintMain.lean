/-
  BlueprintMain

  The generator entry point of the Verso blueprint (`lake exe vbp build`
  discovers this file by name and runs it). It renders the document
  `Blueprint` to `_out/site/html-multi` with the blueprint's preview data.
-/

import VersoManual
import VersoBlueprint.PreviewManifest
import Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
