import Yatima.Typechecker.Datatypes
import Yatima.Datatypes.Store

/-!
# The Typechecker monad

This module defines the typechecker monad `TypecheckM`, together with various utilities to run and
initialize its context.
-/

namespace Yatima.Typechecker

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
  pStore   : PureStore
  deriving Inhabited

/--
The state available to the typechecker monad. The available fields are
* `tcConsts : List (Option Const)` : cache of already-typechecked constants, with their types and values annotated
-/
structure TypecheckState where
  tcConsts : Array (Option Const)
  deriving Inhabited

/-- An initialization of the typchecker context with a particular `store : Array Const` -/
def TypecheckCtx.init (pStore : PureStore) : TypecheckCtx :=
  { (default : TypecheckCtx) with pStore }

/-- An initialization of the typechecker state with a particular `store : Array Const` -/
def TypecheckState.init (pStore : PureStore) : TypecheckState := Id.run $ do
  let mut tcConsts := .mk []
  -- FIXME there's gotta be a better way...
  for _ in [:pStore.consts.size] do
    tcConsts := .mk $ none :: tcConsts.toList
  pure {tcConsts}

/-- An initialization of the typechecker context with a particular `env : Env` and `store : Array Const` -/
def TypecheckCtx.initEnv (env : Env) (pStore : PureStore) : TypecheckCtx :=
  { (default : TypecheckCtx) with pStore, env }

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

def natIndex : TypecheckM Nat := do
  match (← read).pStore.natIdx with | none => throw $ .custom "Cannot find definition of `Nat`" | some a => pure a
def stringIndex : TypecheckM Nat := do
  match (← read).pStore.stringIdx with | none => throw $ .custom "Cannot find definition of `String`" | some a => pure a
def zeroIndexWith (noneHandle : TypecheckM A) (someHandle : Nat → TypecheckM A) : TypecheckM A := do
  match (← read).pStore.natZeroIdx with | none => noneHandle | some a => someHandle a
def succIndexWith (noneHandle : TypecheckM A) (someHandle : Nat → TypecheckM A) : TypecheckM A := do
  match (← read).pStore.natSuccIdx with | none => noneHandle | some a => someHandle a

end Yatima.Typechecker
