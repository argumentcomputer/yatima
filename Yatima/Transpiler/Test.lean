import Yatima.ForLurkRepo.Printing
import Yatima.Transpiler.Transpiler
import Yatima.Compiler.Compiler

open Yatima.Compiler Yatima.FromIpld Yatima.Transpiler

def test : IO Unit := do
  match (← compile "./Fixtures/LurkTranslation/SimplePrelude.lean") with 
    | .error msg => IO.eprintln msg
    | .ok compState =>
      match convertStore compState.store with
        | .error msg => IO.eprintln msg
        | .ok convState => match transpile convState with
          | .error msg => IO.eprintln msg
          | .ok out => IO.println out
