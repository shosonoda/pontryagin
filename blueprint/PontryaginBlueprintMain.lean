import VersoManual
import VersoBlueprint.PreviewManifest
import PontryaginBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc PontryaginBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
