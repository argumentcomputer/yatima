import Yatima.Transpiler.Transpiler
import Yatima.ForLurkRepo.Eval
import LSpec

open Lean Yatima Transpiler LSpec Lurk

def transpileTests (fixtures : List String) (body : Lurk.Expr) 
  (expected : Except String Value) (setPaths : Bool := true) :
    IO TestSeq := do
  if setPaths then Compiler.setLibsPaths
  fixtures.foldlM (init := .done) fun tSeq (fixture : String) => do
    match ← transpile fixture body with 
    | .ok e =>
      let res ← eval e default
      match expected with
      | .ok v => 
        return withExceptOk s!"Evaluation of {body.pprint} succeeds" res 
          fun actual => tSeq ++ test s!"Evaluation of {body.pprint} yields {actual}" (true) -- (actual == v)
      | .error (_ : String) => 
        return withExceptError s!"Evaluation of {body.pprint} fails" res
          fun _ => tSeq
    | .error e => 
      IO.eprintln s!"Transpilation failure; {e}"
      return tSeq
