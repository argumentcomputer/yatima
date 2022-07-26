import LSpec
import Yatima.Compiler.Compiler

open Yatima.Compiler

def succeedOnCompilation (fileName : String) : IO TestSeq := do
  return withExceptOk s!"Compiles {fileName}" (← compile fileName)
    fun _ => .done

def terminationFixtures := [
  "Fixtures/Termination/NastyInductives.lean",
  "Fixtures/Termination/Prelude.lean"
]

def main : IO UInt32 := do
  setLibsPaths
  lspecEachWith terminationFixtures succeedOnCompilation
