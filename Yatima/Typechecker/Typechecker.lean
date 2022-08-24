import Yatima.Typechecker.Infer
import Yatima.Typechecker.TypecheckM
import Yatima.Converter.Converter
import Yatima.Datatypes.Store

namespace Yatima.Typechecker

def typecheckM : TypecheckM Unit := do
  (← read).store.forM checkConst

def typecheckConsts (consts : Array Const) : Except String Unit :=
  match TypecheckM.run (.init consts) typecheckM with
  | .ok u => .ok u
  | .error err => throw $ toString err

def typecheck (store : Ipld.Store) : Except String Unit :=
  match Converter.extractConstArray store with
  | .ok consts => typecheckConsts consts
  | .error msg => throw msg

end Yatima.Typechecker
