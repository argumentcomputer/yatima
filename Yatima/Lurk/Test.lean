import Yatima.Compiler.Frontend

open Yatima.Compiler

def test : IO Unit := do
  let _ ← runFrontend "./Fixtures/LurkTranslation/SimplePrelude.lean"
  IO.println "Print Lurk expr here"

