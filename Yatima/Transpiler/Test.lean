import Yatima.ForLurkRepo.Printing
import Yatima.Transpiler.Transpiler
import Yatima.Compiler.Compiler
import Lean.Util.Path

open System

open Yatima.Compiler Yatima.FromIpld Yatima.Transpiler 

def test : IO Unit := do
  match (← compile "./Fixtures/LurkTranslation/SimplePrelude.lean") with 
    | .error msg => IO.eprintln msg
    | .ok compState => match transpile compState with
      | .error msg => IO.eprintln msg
      | .ok out => 
        let path ← IO.currentDir
        let fname : FilePath := path/ s!"output" |>.withExtension "lurk"
        IO.FS.writeFile fname s!"{out}"
        IO.print out