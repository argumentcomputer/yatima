import Yatima.Typechecker.Infer
import Yatima.Ipld.FromIpld
import Yatima.Datatypes.Store

namespace Yatima.Typechecker

def typecheckM : TypecheckM Unit := do
  let defns := (← read).store
  defns.forM checkConst

def typecheck (store : Ipld.Store) : IO UInt32 :=
  match FromIpld.extractConstArray store with
  | .ok store => match TypecheckM.run (.init store) typecheckM with
    | .ok _ => do
      pure 0
    | .error msg => do
      IO.eprintln s!"{toString msg}"
      pure 1
  | .error msg => do
    IO.eprintln msg
    pure 1

end Yatima.Typechecker
