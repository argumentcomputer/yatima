import Yatima.Compiler.Frontend
import Yatima.ForLurkRepo.Printing
import Yatima.Transpiler.Transpiler

open Yatima.Compiler Lurk

def test : IO Unit := do
  match (← runFrontend "./Fixtures/LurkTranslation/SimplePrelude.lean") with 
    | .ok result => 
      let compiledStore := result.store
      match Yatima.Transpiler.transpile compiledStore with
        | .ok result => IO.println result
        | .error msg => IO.println msg
    | .error msg => IO.println msg

-- Last run:
--(let ((id (lambda (α) (lambda (a) a))) (id:_cstage1 (lambda (α) (lambda (a) a))) (test:recOn (lambda (motive) (lambda (t) (lambda (c1) (lambda (c2) ((((test:rec motive) c1) c2) t))))))) (current-env))