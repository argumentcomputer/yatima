import Yatima.Typechecker.Datatypes
import Yatima.Datatypes.Store

/-!
# The Typechecker monad

This module defines the typechecker monad `TypecheckM`, together with various utilities to run and
initialize its context.
-/

namespace Yatima.Typechecker

open TC

open Lurk (F)

-- FIXME why is this needed if `TC.Store` already derives this?
deriving instance Inhabited for TC.Store

/--
The context available to the typechecker monad. The available fields are
* `lvl : Nat` : Depth of the subterm. Coincides with the length of the list of types
* `env : Env` : A environment of known values, and universe levels. See `Env`
* `types : List (Tunk Value)` : The types of the values in `Env`.
* `store : Array Const` : An array of known constants in the context that can be referred to by their index.
-/
structure TypecheckCtx where
  lvl       : Nat
  env       : Env
  types     : List SusValue
  store     : Store
  const     : Name
  mutTypes  : Std.RBMap F (List Univ → SusValue) compare
  deriving Inhabited

/--
The state available to the typechecker monad. The available fields are
* `tcConsts : List (Option Const)` : cache of already-typechecked constants, with their types and values annotated
-/
structure TypecheckState where
  tcConsts : Array (Option TypedConst)
  deriving Inhabited

/-- An initialization of the typchecker context with a particular `store : Array Const` -/
def TypecheckCtx.init (store : Store) : TypecheckCtx :=
  { (default : TypecheckCtx) with store }

/-- An initialization of the typechecker state with a particular `store : Array Const` -/
def TypecheckState.init (store : Store) : TypecheckState := Id.run $ do
  pure {tcConsts := mkArray store.consts.size none}

/-- An initialization of the typechecker context with a particular `env : Env` and `store : Array Const` -/
def TypecheckCtx.initEnv (env : Env) (store : Store) : TypecheckCtx :=
  { (default : TypecheckCtx) with store, env }

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
def withResetCtx (const : Name) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => {lvl := 0, env := default, types := [], store := ctx.store, const := const, mutTypes := default}

/--
Evaluates a `TypecheckM` computation with the given `mutTypes`.
-/
def withMutTypes (mutTypes : Std.RBMap ConstIdx (List Univ → SusValue) compare) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => {ctx with mutTypes}

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

-- TODO hardcode these maps once we have the hashes
def primsToFs : Std.RBMap PrimConst F compare := sorry
def fsToPrims : Std.RBMap F PrimConst compare := sorry

def primFWith (p : PrimConst) (noneHandle : TypecheckM A) (someHandle : F → TypecheckM A) : TypecheckM A := do
  match primsToFs.find? p with | none => noneHandle | some a => someHandle a
def primF (p : PrimConst) : TypecheckM Nat := do
  primFWith p (throw $ .custom s!"Cannot find constant `{p}` in store") pure
def fPrim (f : F) : TypecheckM (Option PrimConst) := do
  pure $ fsToPrims.find? f

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
