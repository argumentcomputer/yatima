import Yatima.Typechecker.Infer
import Yatima.Ipld.FromIpld
import Yatima.Datatypes.Store

namespace Yatima.Typechecker

def typecheckM : TypecheckM Unit := do
  let defns := (← read).store
  defns.forM checkConst

def typecheck (store : Ipld.Store) : Bool × Option String :=
  match FromIpld.extractConstArray store with
  | .ok store => match TypecheckM.run (.init store) typecheckM with
    | .ok _ => (true, none)
    | .error msg => (false, some s!"{toString msg}")
  | .error msg => (false, some msg)

end Yatima.Typechecker
