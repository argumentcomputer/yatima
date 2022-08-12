import Yatima.Typechecker.TypecheckM
import Yatima.Converter.Converter
import Yatima.Datatypes.Store

namespace Yatima.Typechecker

def typecheckM : TypecheckM Unit :=
  -- TODO: typecheck all constants
  pure ()

def typecheck (store : Ipld.Store) : Bool × Option String :=
  match Converter.extractConstArray store with
  | .ok store => match TypecheckM.run (.init store) typecheckM with
    | .ok _ => (true, none)
    | .error msg => (false, some "toString msg")
  | .error msg => (false, some msg)

end Yatima.Typechecker
