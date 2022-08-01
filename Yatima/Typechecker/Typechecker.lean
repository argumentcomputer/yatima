import Yatima.Typechecker.Infer
import Yatima.Ipld.FromIpld
import Yatima.Datatypes.Store

namespace Yatima.Typechecker

def typecheckM : TypecheckM Unit := do
  let defns := (← read).store
  defns.forM checkConst

def typecheck (defns : Array Const) : Except TypecheckError Unit :=
  TypecheckM.run (.init defns) typecheckM

end Yatima.Typechecker
