import Yatima.ForLurkRepo.Printing
import Yatima.Transpiler.Transpiler
import Yatima.Compiler.Compiler

open Yatima.Compiler Yatima.Typechecker Yatima.Transpiler

def test : IO Unit := do
  match (← compile "./Fixtures/LurkTranslation/SimplePrelude.lean") with 
    | .error msg => IO.println msg
    | .ok compState =>
      match convertStore compState.store with
        | .error msg => IO.println msg
        | .ok convState => match transpile convState with
          | .error msg => IO.println msg
          | .ok out => IO.println out
