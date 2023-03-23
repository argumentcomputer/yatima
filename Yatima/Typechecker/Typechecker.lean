import Yatima.Typechecker.Infer

/-!
# Typechecker

This module defines the user-facing functions for the typechecker.
-/

namespace Yatima.Typechecker

/-- Typechecks all constants from a store -/
def typecheckAll (store : Store) (constNames : ConstNames) : Except String Unit :=
  let aux := do (← read).store.forM fun f _ => checkConst f
  match TypecheckM.run (.init store constNames true) default aux with
  | .ok u => .ok u
  | .error err => throw err

/--
This function is supposed to be transpiled to Lurk, which does `open f` instead
of retrieving constants from a store
-/
-- def typecheckConstNoStore (f : Lurk.F) : Bool :=
--   TypecheckM.run default default (checkConst f) |>.isOk
def typecheckConstNoStore (f : Lurk.F) : Except String Unit :=
  TypecheckM.run default default (checkConst f)

end Yatima.Typechecker
