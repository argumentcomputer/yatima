import LSpec
import Yatima.Compiler.Frontend

open Yatima.Compiler in
def compile (fileName : String) : IO TestSeq := do
  return withExceptOk s!"Compiles {fileName}" (← runFrontend fileName)
    fun _ => .done

def terminationFixtures := [
  "Fixtures/Termination/NastyInductives.lean",
  "Fixtures/Termination/Prelude.lean"
]

def main : IO UInt32 :=
  lspecEachWith terminationFixtures compile
