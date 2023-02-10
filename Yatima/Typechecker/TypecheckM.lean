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
  /-- Maps a variable index (which represents a reference to a mutual const)
    to the hash of that constant (in `TypecheckState.typedConsts`) and
    a function returning a `SusValue` for that constant's type given a list of universes. -/
  mutTypes : Std.RBMap Nat (F × (List Univ → SusValue)) compare
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
abbrev TypecheckM := ReaderT TypecheckCtx $ StateT TypecheckState $ ExceptT String Id

/-- Basic runner for the typechecker monad -/
def TypecheckM.run (ctx : TypecheckCtx) (stt : TypecheckState) (m : TypecheckM α) : Except String α :=
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
def withMutTypes (mutTypes : Std.RBMap Nat (F × (List Univ → SusValue)) compare) :
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
  | .op .natBlt => return .ofNat 1253606988906390666
  | .op .natBle => return .ofNat 2316364997730606639
  | .string => return .ofNat 856105669419039816
  | .op .natBeq => return .ofNat 13525232381600327665
  | .boolTrue => return .ofNat 6498689371378585742
  | .nat => return .ofNat 3995350730059356211
  | .op .natPow => return .ofNat 9160466645096263850
  | .bool => return .ofNat 9037663241488537835
  | .natZero => return .ofNat 8341451706878890052
  | .op .natMul => return .ofNat 16639832249204894856
  | .boolFalse => return .ofNat 16485885058083788770
  | .op .natSucc => return .ofNat 13457438356937304886
  | .op .natAdd => return .ofNat 16245233664916364549
def fToPrim : F → Option PrimConst
  | .ofNat 1253606988906390666 => return .op .natBlt
  | .ofNat 2316364997730606639 => return .op .natBle
  | .ofNat 856105669419039816 => return .string
  | .ofNat 13525232381600327665 => return .op .natBeq
  | .ofNat 6498689371378585742 => return .boolTrue
  | .ofNat 3995350730059356211 => return .nat
  | .ofNat 9160466645096263850 => return .op .natPow
  | .ofNat 9037663241488537835 => return .bool
  | .ofNat 8341451706878890052 => return .natZero
  | .ofNat 16639832249204894856 => return .op .natMul
  | .ofNat 16485885058083788770 => return .boolFalse
  | .ofNat 13457438356937304886 => return .op .natSucc
  | .ofNat 16245233664916364549 => return .op .natAdd
  | _ => none
def primToFQuick : PrimConst → Option F
  | .op .natBlt => return .ofNat 7251320430134650332
  | .op .natBle => return .ofNat 10102183310689148260
  | .string => return .ofNat 6949939019387688787
  | .op .natBeq => return .ofNat 9760045753923099497
  | .boolTrue => return .ofNat 3531769586140967142
  | .nat => return .ofNat 36261279848039267
  | .op .natPow => return .ofNat 13557009730483185550
  | .bool => return .ofNat 12141209139639517940
  | .natZero => return .ofNat 18332866130654683503
  | .op .natMul => return .ofNat 16426412488492540244
  | .boolFalse => return .ofNat 7441924181250763784
  | .op .natSucc => return .ofNat 11811367283875677477
  | .op .natAdd => return .ofNat 2584543329451145240
def fToPrimQuick : F → Option PrimConst
  | .ofNat 7251320430134650332 => return .op .natBlt
  | .ofNat 10102183310689148260 => return .op .natBle
  | .ofNat 6949939019387688787 => return .string
  | .ofNat 9760045753923099497 => return .op .natBeq
  | .ofNat 3531769586140967142 => return .boolTrue
  | .ofNat 36261279848039267 => return .nat
  | .ofNat 13557009730483185550 => return .op .natPow
  | .ofNat 12141209139639517940 => return .bool
  | .ofNat 18332866130654683503 => return .natZero
  | .ofNat 16426412488492540244 => return .op .natMul
  | .ofNat 7441924181250763784 => return .boolFalse
  | .ofNat 11811367283875677477 => return .op .natSucc
  | .ofNat 2584543329451145240 => return .op .natAdd
  | _ => none
--PRIMEND

def primFWith (p : PrimConst) (noneHandle : TypecheckM α)
    (someHandle : F → TypecheckM α) : TypecheckM α := do
  if !(← read).quick then
    match primToF p with | none => noneHandle | some a => someHandle a
  else match primToFQuick p with | none => noneHandle | some a => someHandle a

def primF (p : PrimConst) : TypecheckM F :=
  primFWith p (throw s!"Cannot find constant `{p}` in store") pure

def fPrim (f : F) : TypecheckM $ Option PrimConst := do
  if !(← read).quick then pure $ fToPrim f
  else pure $ fToPrimQuick f

structure PrimOp where
  op : Array SusValue → TypecheckM (Option Value)

def PrimConstOp.toPrimOp : PrimConstOp → PrimOp
  | .natSucc => .mk fun vs => do
    let some v := vs.get? 0
      | throw "At least one SusValue element needed for PrimConstOp.natSucc"
    match v.get with
    | .lit (.natVal v) => pure $ .some $ .lit (.natVal v.succ)
    | _ => pure none
  | .natAdd => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two SusValue elements needed for PrimConstOp.natAdd"
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') => pure $ .some $ .lit (.natVal (v+v'))
    | _, _ => pure none
  | .natMul => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two SusValue elements needed for PrimConstOp.natMul"
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') => pure $ .some $ .lit (.natVal (v*v'))
    | _, _ => pure none
  | .natPow => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two SusValue elements needed for PrimConstOp.natPow"
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') => pure $ .some $ .lit (.natVal (Nat.pow v v'))
    | _, _ => pure none
  | .natBeq => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two SusValue elements needed for PrimConstOp.natBeq"
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v = v' then do
        pure $ some $ .app (.const (← primF .boolTrue) []) []
      else do
        pure $ some $ .app (.const (← primF .boolFalse) []) []
    | _, _ => pure none
  | .natBle => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two SusValue elements needed for PrimConstOp.natBle"
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v ≤ v' then do
        pure $ some $ .app (.const (← primF .boolTrue) []) []
      else do
        pure $ some $ .app (.const (← primF .boolFalse) []) []
    | _, _ => pure none
  | .natBlt => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two SusValue elements needed for PrimConstOp.natBlt"
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v < v' then do
        pure $ some $ .app (.const (← primF .boolTrue) []) []
      else do
        pure $ some $ .app (.const (← primF .boolFalse) []) []
    | _, _ => pure none

end Yatima.Typechecker
