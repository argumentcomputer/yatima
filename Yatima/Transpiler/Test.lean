import Yatima.ForLurkRepo.Printing
import Yatima.Transpiler.Transpiler
import Yatima.Compiler.Compiler

open Yatima.Compiler Yatima.Transpiler

def test : IO Unit := do
  match (← compile "./Fixtures/LurkTranslation/SimplePrelude.lean") with 
    | .error msg => IO.eprintln msg
    | .ok compState => match transpile compState with
      | .error msg => IO.eprintln msg
      | .ok out => IO.println out

#eval test