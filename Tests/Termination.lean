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
  terminationFixtures.foldlM (init := 0) fun acc fileName => do
    let tSeq ← compile fileName
    pure $ min 1 (acc + (← lspec tSeq))
