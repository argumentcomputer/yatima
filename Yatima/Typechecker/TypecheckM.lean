import Yatima.Typechecker.Datatypes
import Yatima.Datatypes.Store

/-!
# The Typechecker monad

This module defines the typechecker monad `TypecheckM`, together with various utilities to run and
initialize its environment.
-/

namespace Yatima.Typechecker

/--
The environment available to the typechecker monad. The available fields are
* `lvl : Nat` : TODO: Get clarification on this.
* `ctx : Context` : A context of known values, and universe levels. See `Context`
* `types : List (Tunk Value)` : The types of the values in `Context`.
* `store : Array Const` : An array of known constants in the environment that can be referred to by their index.
-/
structure TypecheckEnv where
  lvl    : Nat
  ctx    : Context
  types  : List (Thunk Value)
  pStore : PureStore
  deriving Inhabited

/-- An initialization of the typchecker environment with a particular `store : Array Const` -/
def TypecheckEnv.init (pStore : PureStore) : TypecheckEnv :=
  { (default : TypecheckEnv) with pStore }

/-- An initialization of the typechecker environment with a particular `ctx : Context` and `store : Array Const` -/
def TypecheckEnv.initCtx (ctx : Context) (pStore : PureStore) : TypecheckEnv :=
  { (default : TypecheckEnv) with pStore, ctx }

/--
The monad where the typechecking is done is a stack of a `ReaderT` that can access a `TypecheckEnv`,
and can throw exceptions of the form `TypecheckError`
-/
abbrev TypecheckM := ReaderT TypecheckEnv $ ExceptT TypecheckError Id

/-- Basic runner for the typchecker monad -/
def TypecheckM.run (env : TypecheckEnv) (m : TypecheckM α) : Except TypecheckError α :=
  ExceptT.run (ReaderT.run m env)

/-- Evaluates a `TypecheckM` computation with an `TypecheckEnv` whose context is fixed by `ctx` -/
def withCtx (ctx : Context) : TypecheckM α → TypecheckM α :=
  withReader fun env => { env with ctx := ctx }

/--
Evaluates a `TypecheckM` computation with a `TypecheckEnv` which has been extended with an additional
`val : Thunk Value`, `typ : Thunk Type` pair.

The `lvl` of the `TypecheckEnv` is also incremented.
TODO: Get clarification on this.
-/
def withExtendedEnv (val typ : Thunk Value) : TypecheckM α → TypecheckM α :=
  withReader fun env => { env with
    lvl := env.lvl + 1,
    types := typ :: env.types,
    ctx := env.ctx.extendWith val }

/--
Evaluates a `TypecheckM` computation with a `TypecheckEnv` with a the context extended by a
`thunk : Thunk Value` (whose type is not known, unlike `withExtendedEnv`)
-/
def withExtendedCtx (thunk : Thunk Value) : TypecheckM α → TypecheckM α :=
  withReader fun env => { env with ctx := env.ctx.extendWith thunk }

/--
Evaluates a `TypecheckM` computation with a `TypecheckEnv` whose context is an extension of `ctx`
by a `thunk : Thunk Value` (whose type is not known)
-/
def withNewExtendedCtx (ctx : Context) (thunk : Thunk Value) :
    TypecheckM α → TypecheckM α :=
  withReader fun env => { env with ctx := ctx.extendWith thunk }

/--
Evaluates a `TypecheckM` computation with a `TypecheckEnv` whose context is an extension of `ctx`
by a free variable with name `name : Name`, de-Bruijn index `i : Nat`, and type `type : ThunK Value`
-/
def withNewExtendedCtxByVar (ctx : Context) (name : Name) (i : Nat) (type : Thunk Value) :
    TypecheckM α → TypecheckM α :=
  withNewExtendedCtx ctx (mkVar name i type)

def natIndex : TypecheckM Nat := do
  match (← read).pStore.natIdx with | none => throw $ .custom "Cannot find definition of `Nat`" | some a => pure a
def stringIndex : TypecheckM Nat := do
  match (← read).pStore.stringIdx with | none => throw $ .custom "Cannot find definition of `String`" | some a => pure a
def zeroIndex : TypecheckM Nat := do
  match (← read).pStore.natZeroIdx with | none => throw $ .custom "Cannot find definition of `Nat.Zero`" | some a => pure a
def succIndex : TypecheckM Nat := do
  match (← read).pStore.natSuccIdx with | none => throw $ .custom "Cannot find definition of `Nat.Succ`" | some a => pure a

end Yatima.Typechecker
