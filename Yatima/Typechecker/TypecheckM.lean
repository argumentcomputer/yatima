import Yatima.Typechecker.Datatypes
import Yatima.Common.Store
import Std.Data.RBMap

/-!
# The Typechecker monad

This module defines the typechecker monad `TypecheckM`, together with various utilities to run and
initialize its context.
-/

namespace Yatima.Typechecker

open TC
open Lurk (F)

/--
The context available to the typechecker monad. The available fields are
* `lvl : Nat` : Depth of the subterm. Coincides with the length of the list of types
* `env : Env` : A environment of known values, and universe levels. See `Env`
* `types : List (Tunk Value)` : The types of the values in `Env`.
* `store : Array Const` : An array of known constants in the context that can be referred to by their index.
-/
structure TypecheckCtx where
  lvl      : Nat
  env      : Env
  types    : List SusValue
  store    : Store
  mutTypes : Std.RBMap F (List Univ → SusValue) compare
  quick    : Bool
  deriving Inhabited

/--
The state available to the typechecker monad. The available fields are
* `typedConsts` : cache of already-typechecked constants, with their types and
values annotated
-/
structure TypecheckState where
  typedConsts : Std.RBMap F TypedConst compare
  deriving Inhabited

/-- An initialization of the typchecker context with a particular store -/
def TypecheckCtx.init (store : Store) (quick : Bool) : TypecheckCtx :=
  { (default : TypecheckCtx) with store := store, quick := quick }

/--
The monad where the typechecking is done is a stack of a `ReaderT` that can access a `TypecheckCtx`,
and can throw exceptions of the form `TypecheckError`
-/
abbrev TypecheckM := ReaderT TypecheckCtx $ StateT TypecheckState $ ExceptT TypecheckError Id

/-- Basic runner for the typechecker monad -/
def TypecheckM.run (ctx : TypecheckCtx) (stt : TypecheckState) (m : TypecheckM α) : Except TypecheckError α :=
  match ExceptT.run $ (StateT.run (ReaderT.run m ctx) stt) with
  | .error e => .error e
  | .ok (a, _) => .ok a

/-- Evaluates a `TypecheckM` computation with an `TypecheckCtx` whose environment is fixed by `env` -/
def withEnv (env : Env) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with env := env }

/--
Evaluates a `TypecheckM` computation with a reset `TypecheckCtx`.
-/
def withResetCtx : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with
    lvl := 0, env := default, types := default, mutTypes := default }

/--
Evaluates a `TypecheckM` computation with the given `mutTypes`.
-/
def withMutTypes (mutTypes : Std.RBMap F (List Univ → SusValue) compare) :
    TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with mutTypes := mutTypes }

/--
Evaluates a `TypecheckM` computation with a `TypecheckCtx` which has been extended with an additional
`val : SusValue`, `typ : SusValue` pair.

The `lvl` of the `TypecheckCtx` is also incremented.
TODO: Get clarification on this.
-/
def withExtendedCtx (val typ : SusValue) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with
    lvl := ctx.lvl + 1,
    types := typ :: ctx.types,
    env := ctx.env.extendWith val }

/--
Evaluates a `TypecheckM` computation with a `TypecheckCtx` with a the environment extended by a
`thunk : SusValue` (whose type is not known, unlike `withExtendedCtx`)
-/
def withExtendedEnv (thunk : SusValue) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with env := ctx.env.extendWith thunk }

/--
Evaluates a `TypecheckM` computation with a `TypecheckCtx` whose environment is an extension of `env`
by a `thunk : SusValue` (whose type is not known)
-/
def withNewExtendedEnv (env : Env) (thunk : SusValue) :
    TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with env := env.extendWith thunk }

--PRIMBEGIN
def primToF : PrimConst → Option F
  | .op .natBle  => return .ofNat 10
  | .string      => return .ofNat 5
  | .nat         => return .ofNat 0
  | .bool        => return .ofNat 1
  | .boolTrue    => return .ofNat 2
  | .boolFalse   => return .ofNat 3
  | .natZero     => return .ofNat 4
  | .op .natAdd  => return .ofNat 6
  | .op .natMul  => return .ofNat 7
  | .op .natPow  => return .ofNat 8
  | .op .natBeq  => return .ofNat 9
  | .op .natBlt  => return .ofNat 11
  | .op .natSucc => return .ofNat 12
def fToPrim : F → Option PrimConst
  | .ofNat 0 => sorry
  | .ofNat 1 => sorry
  | .ofNat 2 => sorry
  | .ofNat 3 => sorry
  | .ofNat 4 => sorry
  | .ofNat 5 => sorry
  | .ofNat 6 => sorry
  | .ofNat 7 => sorry
  | .ofNat 8 => sorry
  | .ofNat 9 => sorry
  | .ofNat 10 => sorry
  | .ofNat 11 => sorry
  | .ofNat 12 => sorry
  | _ => none
def primToFQuick : PrimConst → Option F
  | .nat         => return .ofNat 0
  | .bool        => return .ofNat 1
  | .boolTrue    => return .ofNat 2
  | .boolFalse   => return .ofNat 3
  | .natZero     => return .ofNat 4
  | .string      => return .ofNat 5
  | .op .natAdd  => return .ofNat 6
  | .op .natMul  => return .ofNat 7
  | .op .natPow  => return .ofNat 8
  | .op .natBeq  => return .ofNat 9
  | .op .natBle  => return .ofNat 10
  | .op .natBlt  => return .ofNat 11
  | .op .natSucc => return .ofNat 12
def fToPrimQuick : F → Option PrimConst
  | .ofNat 0 => sorry
  | .ofNat 1 => sorry
  | .ofNat 2 => sorry
  | .ofNat 3 => sorry
  | .ofNat 4 => sorry
  | .ofNat 5 => sorry
  | .ofNat 6 => sorry
  | .ofNat 7 => sorry
  | .ofNat 8 => sorry
  | .ofNat 9 => sorry
  | .ofNat 10 => sorry
  | .ofNat 11 => sorry
  | .ofNat 12 => sorry
  | _ => none
--PRIMEND

def primFWith (p : PrimConst) (noneHandle : TypecheckM α)
    (someHandle : F → TypecheckM α) : TypecheckM α := do
  if !(← read).quick then
    match primToF p with | none => noneHandle | some a => someHandle a
  else match primToFQuick p with | none => noneHandle | some a => someHandle a

def primF (p : PrimConst) : TypecheckM F :=
  primFWith p (throw $ .custom s!"Cannot find constant `{p}` in store") pure

def fPrim (f : F) : TypecheckM $ Option PrimConst := do
  if !(← read).quick then pure $ fToPrim f
  else pure $ fToPrimQuick f

structure PrimOp where
  op : Array SusValue → TypecheckM (Option Value)

def PrimConstOp.toPrimOp : PrimConstOp → PrimOp
  | .natSucc => .mk fun vs => do
    let some v := vs.get? 0 | throw $ .impossible
    match v.get with
    | .lit (.natVal v) => pure $ .some $ .lit (.natVal (v+1))
    | _ => pure none
  | .natAdd => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1) | throw $ .impossible
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') => pure $ .some $ .lit (.natVal (v+v'))
    | _, _ => pure none
  | .natMul => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1) | throw $ .impossible
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') => pure $ .some $ .lit (.natVal (v*v'))
    | _, _ => pure none
  | .natPow => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1) | throw $ .impossible
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') => pure $ .some $ .lit (.natVal (Nat.pow v v'))
    | _, _ => pure none
  | .natBeq => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1) | throw $ .impossible
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v = v' then do
        pure $ some $ .app (.const (← primF .boolTrue) []) []
      else do
        pure $ some $ .app (.const (← primF .boolFalse) []) []
    | _, _ => pure none
  | .natBle => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1) | throw $ .impossible
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v ≤ v' then do
        pure $ some $ .app (.const (← primF .boolTrue) []) []
      else do
        pure $ some $ .app (.const (← primF .boolFalse) []) []
    | _, _ => pure none
  | .natBlt => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1) | throw $ .impossible
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v < v' then do
        pure $ some $ .app (.const (← primF .boolTrue) []) []
      else do
        pure $ some $ .app (.const (← primF .boolFalse) []) []
    | _, _ => pure none

end Yatima.Typechecker
