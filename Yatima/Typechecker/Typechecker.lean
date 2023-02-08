import Yatima.Typechecker.Infer

/-!
# Typechecker

This module defines the user-facing functions for the typechecker.
-/

namespace Yatima.Typechecker

open TC

/-- Typechecks all constants from a `Yatima.TC.Store` -/
def typecheckAll (store : Store) : Except String Unit :=
  let aux := do (← read).store.forM fun f _ => checkConst f
  match TypecheckM.run (.init store true) default aux with
  | .ok u => .ok u
  | .error err => throw err

open Lurk (F)

/--
This function is supposed to be transpiled to Lurk, which does `open f` instead
of retrieving constants from a `Yatima.TC.Store`
-/
def typecheckConstNoStore (f : F) : Except String Unit :=
  match TypecheckM.run default default (checkConst f) with
  | .ok u => .ok u
  | .error err => throw err

end Yatima.Typechecker
