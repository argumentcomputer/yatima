import Yatima.Typechecker.Infer
import Yatima.Typechecker.TypecheckM
import Yatima.Converter.Converter
import Yatima.Datatypes.Store

namespace Yatima.Typechecker

def typecheckM : TypecheckM Unit := do
  (← read).store.forM checkConst

def typecheck (consts : Array Const) : Except TypecheckError Unit :=
  TypecheckM.run (.init consts) typecheckM

end Yatima.Typechecker
