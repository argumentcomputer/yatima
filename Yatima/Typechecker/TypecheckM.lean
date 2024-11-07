import Yatima.Typechecker.Datatypes
import Batteries.Data.RBMap

/-!
# The Typechecker monad

This module defines the typechecker monad `TypecheckM`, together with various utilities to run and
initialize its context.
-/

namespace Yatima.Typechecker

open IR
open Lurk (F Digest)

abbrev RecrCtx    := Batteries.RBMap Nat (Digest × (List Univ → SusValue)) compare
abbrev ConstNames := Batteries.RBMap Digest Lean.Name compare
abbrev Store      := Batteries.RBMap Digest Const compare

/--
The context available to the typechecker monad. The available fields are
* `lvl : Nat` : Depth of the subterm. Coincides with the length of the list of types
* `env : Env` : A environment of known values, and universe levels. See `Env`
* `types : List SusValue` : The types of the values in `Env`.
* `store : Store` : An store of known constants in the context.
-/
structure TypecheckCtx where
  lvl         : Nat
  env         : Env
  types       : List SusValue
  store       : Store
  /-- Maps a variable index (which represents a reference to a mutual const)
    to the hash of that constant (in `TypecheckState.typedConsts`) and
    a function returning a `SusValue` for that constant's type given a list of universes. -/
  mutTypes    : RecrCtx
  constNames  : ConstNames
  limitAxioms : Bool
  recF?       : Option Digest
  quick       : Bool
  dbg         : Bool := false
  deriving Inhabited

/--
The state available to the typechecker monad. The available fields are
* `typedConsts` : cache of already-typechecked constants, with their types and
  values annotated
-/
structure TypecheckState where
  typedConsts : Batteries.RBMap Digest TypedConst compare
  deriving Inhabited

/-- An initialization of the typchecker context with a particular store -/
def TypecheckCtx.init (store : Store) (constNames : ConstNames) (quick : Bool) :
    TypecheckCtx :=
  { (default : TypecheckCtx) with
    store      := store,
    constNames := constNames,
    quick      := quick }

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
    lvl := 0, env := default, types := default, mutTypes := default, recF? := none }

/--
Evaluates a `TypecheckM` computation with the given `mutTypes`.
-/
def withMutTypes (mutTypes : RecrCtx) :
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

def withLimitedAxioms : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with limitAxioms := true }

def withRecF (f : Digest) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with recF? := some f }

/--
Evaluates a `TypecheckM` computation with a `TypecheckCtx` whose environment is an extension of `env`
by a `thunk : SusValue` (whose type is not known)
-/
def withDbg : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with dbg := true }

def tc_trace (msg : String) : TypecheckM Unit := do
  if (← read).dbg then dbg_trace msg

--PIN
def primToF : PrimConst → Option Digest
  | .op .natBlt => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .op .natBle => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .string => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .op .natBeq => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .boolTrue => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .nat => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .op .natPow => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .bool => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .natZero => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .op .natMul => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .boolFalse => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .op .natSucc => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]
  | .op .natAdd => .some #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0]

def fToPrim (digest : Digest) : Option PrimConst :=
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.op .natBlt) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.op .natBle) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.string) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.op .natBeq) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.boolTrue) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.nat) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.op .natPow) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.bool) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.natZero) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.op .natMul) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.boolFalse) else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then .some (.op .natSucc) else
.none


def primToFQuick : PrimConst → Option Digest
  | .op .natBlt => .some #[.ofNat 36, .ofNat 20, .ofNat 134, .ofNat 195, .ofNat 244, .ofNat 212, .ofNat 10, .ofNat 122]
  | .op .natBle => .some #[.ofNat 48, .ofNat 152, .ofNat 239, .ofNat 140, .ofNat 231, .ofNat 21, .ofNat 189, .ofNat 88]
  | .string => .some #[.ofNat 253, .ofNat 244, .ofNat 183, .ofNat 126, .ofNat 229, .ofNat 210, .ofNat 141, .ofNat 20]
  | .op .natBeq => .some #[.ofNat 123, .ofNat 68, .ofNat 0, .ofNat 122, .ofNat 38, .ofNat 88, .ofNat 18, .ofNat 16]
  | .boolTrue => .some #[.ofNat 177, .ofNat 156, .ofNat 210, .ofNat 52, .ofNat 181, .ofNat 92, .ofNat 77, .ofNat 47]
  | .nat => .some #[.ofNat 29, .ofNat 200, .ofNat 205, .ofNat 196, .ofNat 220, .ofNat 52, .ofNat 29, .ofNat 63]
  | .op .natPow => .some #[.ofNat 45, .ofNat 245, .ofNat 94, .ofNat 3, .ofNat 250, .ofNat 75, .ofNat 198, .ofNat 229]
  | .bool => .some #[.ofNat 32, .ofNat 199, .ofNat 24, .ofNat 210, .ofNat 52, .ofNat 75, .ofNat 5, .ofNat 6]
  | .natZero => .some #[.ofNat 22, .ofNat 196, .ofNat 111, .ofNat 99, .ofNat 245, .ofNat 179, .ofNat 163, .ofNat 136]
  | .op .natMul => .some #[.ofNat 249, .ofNat 91, .ofNat 96, .ofNat 111, .ofNat 246, .ofNat 41, .ofNat 92, .ofNat 252]
  | .boolFalse => .some #[.ofNat 10, .ofNat 134, .ofNat 23, .ofNat 163, .ofNat 240, .ofNat 177, .ofNat 152, .ofNat 197]
  | .op .natSucc => .some #[.ofNat 52, .ofNat 122, .ofNat 186, .ofNat 87, .ofNat 3, .ofNat 159, .ofNat 3, .ofNat 107]
  | .op .natAdd => .some #[.ofNat 175, .ofNat 28, .ofNat 120, .ofNat 150, .ofNat 196, .ofNat 122, .ofNat 199, .ofNat 139]

def fToPrimQuick (digest : Digest) : Option PrimConst :=
if digest == #[.ofNat 36, .ofNat 20, .ofNat 134, .ofNat 195, .ofNat 244, .ofNat 212, .ofNat 10, .ofNat 122] then .some (.op .natBlt) else
if digest == #[.ofNat 48, .ofNat 152, .ofNat 239, .ofNat 140, .ofNat 231, .ofNat 21, .ofNat 189, .ofNat 88] then .some (.op .natBle) else
if digest == #[.ofNat 253, .ofNat 244, .ofNat 183, .ofNat 126, .ofNat 229, .ofNat 210, .ofNat 141, .ofNat 20] then .some (.string) else
if digest == #[.ofNat 123, .ofNat 68, .ofNat 0, .ofNat 122, .ofNat 38, .ofNat 88, .ofNat 18, .ofNat 16] then .some (.op .natBeq) else
if digest == #[.ofNat 177, .ofNat 156, .ofNat 210, .ofNat 52, .ofNat 181, .ofNat 92, .ofNat 77, .ofNat 47] then .some (.boolTrue) else
if digest == #[.ofNat 29, .ofNat 200, .ofNat 205, .ofNat 196, .ofNat 220, .ofNat 52, .ofNat 29, .ofNat 63] then .some (.nat) else
if digest == #[.ofNat 45, .ofNat 245, .ofNat 94, .ofNat 3, .ofNat 250, .ofNat 75, .ofNat 198, .ofNat 229] then .some (.op .natPow) else
if digest == #[.ofNat 32, .ofNat 199, .ofNat 24, .ofNat 210, .ofNat 52, .ofNat 75, .ofNat 5, .ofNat 6] then .some (.bool) else
if digest == #[.ofNat 22, .ofNat 196, .ofNat 111, .ofNat 99, .ofNat 245, .ofNat 179, .ofNat 163, .ofNat 136] then .some (.natZero) else
if digest == #[.ofNat 249, .ofNat 91, .ofNat 96, .ofNat 111, .ofNat 246, .ofNat 41, .ofNat 92, .ofNat 252] then .some (.op .natMul) else
if digest == #[.ofNat 10, .ofNat 134, .ofNat 23, .ofNat 163, .ofNat 240, .ofNat 177, .ofNat 152, .ofNat 197] then .some (.boolFalse) else
if digest == #[.ofNat 52, .ofNat 122, .ofNat 186, .ofNat 87, .ofNat 3, .ofNat 159, .ofNat 3, .ofNat 107] then .some (.op .natSucc) else
.none


def allowedAxiom (digest : Digest) : Bool :=
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then true else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then true else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then true else
if digest == #[.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0] then true else
false


def allowedAxiomQuick (digest : Digest) : Bool :=
if digest == #[.ofNat 210, .ofNat 226, .ofNat 162, .ofNat 181, .ofNat 17, .ofNat 138, .ofNat 38, .ofNat 22] then true else
if digest == #[.ofNat 231, .ofNat 219, .ofNat 215, .ofNat 220, .ofNat 213, .ofNat 228, .ofNat 207, .ofNat 173] then true else
if digest == #[.ofNat 12, .ofNat 21, .ofNat 137, .ofNat 22, .ofNat 58, .ofNat 13, .ofNat 173, .ofNat 168] then true else
if digest == #[.ofNat 114, .ofNat 14, .ofNat 145, .ofNat 8, .ofNat 185, .ofNat 23, .ofNat 235, .ofNat 166] then true else
false


--PIN

def primFWith (p : PrimConst) (noneHandle : TypecheckM α)
    (someHandle : Digest → TypecheckM α) : TypecheckM α := do
  if !(← read).quick then
    match primToF p with | none => noneHandle | some a => someHandle a
  else match primToFQuick p with | none => noneHandle | some a => someHandle a

def primF (p : PrimConst) : TypecheckM Digest :=
  primFWith p (throw s!"Cannot find constant `{p}` in store") pure

def fPrim (f : Digest) : TypecheckM $ Option PrimConst := do
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
        pure $ some $ .neu (.const (← primF .boolTrue) [])
      else do
        pure $ some $ .neu (.const (← primF .boolFalse) [])
    | _, _ => pure none
  | .natBle => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two SusValue elements needed for PrimConstOp.natBle"
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v ≤ v' then do
        pure $ some $ .neu (.const (← primF .boolTrue) [])
      else do
        pure $ some $ .neu (.const (← primF .boolFalse) [])
    | _, _ => pure none
  | .natBlt => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two SusValue elements needed for PrimConstOp.natBlt"
    match v.get, v'.get with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v < v' then do
        pure $ some $ .neu (.const (← primF .boolTrue) [])
      else do
        pure $ some $ .neu (.const (← primF .boolFalse) [])
    | _, _ => pure none

end Yatima.Typechecker
