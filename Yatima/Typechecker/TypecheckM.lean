import Yatima.Typechecker.Datatypes
import Batteries.Data.RBMap

/-!
# The Typechecker monad

This module defines the typechecker monad `TypecheckM`, together with various utilities to run and
initialize its context.
-/

namespace Yatima.Typechecker

open IR
open Lurk (F)

abbrev RecrCtx    := Batteries.RBMap Nat (F × (List Univ → SusValue)) compare
abbrev ConstNames := Batteries.RBMap F Lean.Name compare
abbrev Store      := Batteries.RBMap F Const compare

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
  recF?       : Option F
  quick       : Bool
  dbg         : Bool := false
  deriving Inhabited

/--
The state available to the typechecker monad. The available fields are
* `typedConsts` : cache of already-typechecked constants, with their types and
  values annotated
-/
structure TypecheckState where
  typedConsts : Batteries.RBMap F TypedConst compare
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

def withRecF (f : F) : TypecheckM α → TypecheckM α :=
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
def primToF : PrimConst → Option F
  | .op .natBlt => return .ofNat 0x1d1157688c2c860089bd47e1fd290d32cb6ad280c3fdee2f6071df2efce99077
  | .op .natBle => return .ofNat 0x2d9f468676f4b73642a4ef82ee4084925820f865dedcc57db32130861ad54b81
  | .string => return .ofNat 0x17828b7ace2a5a8fd6bcaf82e5e322d66ba36c3272b7b03acd7f1a7ceb37604d
  | .op .natBeq => return .ofNat 0x34ef2714c521c7e4d6576a61a352af530e4f9245146dab92796f043e93e992f1
  | .boolTrue => return .ofNat 0x2fbd0370374f24cc508b864ead8dfedf02f2379ed86004f51cf34ab0fd7e96e2
  | .nat => return .ofNat 0x33d37cd51a12b79a4bb8831b68997c21c446430a0849ae9481ef3644b532545c
  | .op .natPow => return .ofNat 0x2567c615cd722c73fcddd4362938141251eae4d0df4b93c6be07a210ac5bca25
  | .bool => return .ofNat 0x199eb1cdbf5121a37122dd68666c3dccceca4fbc661f3a7bcf3d3549a916f5db
  | .natZero => return .ofNat 0x36fcccf8a02472abe02a8a6f4a8cc54e76268275a00ef7cfe644694c827c6f74
  | .op .natMul => return .ofNat 0x0e5f0761a042e6b9b9d5333cf5d7b6308d9c3c1bfaee9599e82e69bd0163259d
  | .boolFalse => return .ofNat 0x243ab3653bc8479149b60ec2147ff4a5fa036805561c68d485b1422205986966
  | .op .natSucc => return .ofNat 0x3fef544888eb8d71789a4b163c8e8c41bdc37dc835d861b0876c9c66a0c30519
  | .op .natAdd => return .ofNat 0x1dba42b440d4fd17ef127207171ef74d16fac5741f5cddd3e4eae15ff5f3299e
def fToPrim : F → Option PrimConst
  | .ofNat 0x1d1157688c2c860089bd47e1fd290d32cb6ad280c3fdee2f6071df2efce99077 => return .op .natBlt
  | .ofNat 0x2d9f468676f4b73642a4ef82ee4084925820f865dedcc57db32130861ad54b81 => return .op .natBle
  | .ofNat 0x17828b7ace2a5a8fd6bcaf82e5e322d66ba36c3272b7b03acd7f1a7ceb37604d => return .string
  | .ofNat 0x34ef2714c521c7e4d6576a61a352af530e4f9245146dab92796f043e93e992f1 => return .op .natBeq
  | .ofNat 0x2fbd0370374f24cc508b864ead8dfedf02f2379ed86004f51cf34ab0fd7e96e2 => return .boolTrue
  | .ofNat 0x33d37cd51a12b79a4bb8831b68997c21c446430a0849ae9481ef3644b532545c => return .nat
  | .ofNat 0x2567c615cd722c73fcddd4362938141251eae4d0df4b93c6be07a210ac5bca25 => return .op .natPow
  | .ofNat 0x199eb1cdbf5121a37122dd68666c3dccceca4fbc661f3a7bcf3d3549a916f5db => return .bool
  | .ofNat 0x36fcccf8a02472abe02a8a6f4a8cc54e76268275a00ef7cfe644694c827c6f74 => return .natZero
  | .ofNat 0x0e5f0761a042e6b9b9d5333cf5d7b6308d9c3c1bfaee9599e82e69bd0163259d => return .op .natMul
  | .ofNat 0x243ab3653bc8479149b60ec2147ff4a5fa036805561c68d485b1422205986966 => return .boolFalse
  | .ofNat 0x3fef544888eb8d71789a4b163c8e8c41bdc37dc835d861b0876c9c66a0c30519 => return .op .natSucc
  | .ofNat 0x1dba42b440d4fd17ef127207171ef74d16fac5741f5cddd3e4eae15ff5f3299e => return .op .natAdd
  | _ => none
def primToFQuick : PrimConst → Option F
  | .op .natBlt => return .ofNat 4822643605371257236
  | .op .natBle => return .ofNat 2951728617574817879
  | .string => return .ofNat 16001121964852037297
  | .op .natBeq => return .ofNat 12809246696557140246
  | .boolTrue => return .ofNat 17049977161890552712
  | .nat => return .ofNat 12846390003443303075
  | .op .natPow => return .ofNat 14613595360914645637
  | .bool => return .ofNat 7893555430612621797
  | .natZero => return .ofNat 14735850464179338479
  | .op .natMul => return .ofNat 5082277153363671981
  | .boolFalse => return .ofNat 16195091492847522412
  | .op .natSucc => return .ofNat 6836287016865057964
  | .op .natAdd => return .ofNat 14029550093476971811
def fToPrimQuick : F → Option PrimConst
  | .ofNat 4822643605371257236 => return .op .natBlt
  | .ofNat 2951728617574817879 => return .op .natBle
  | .ofNat 16001121964852037297 => return .string
  | .ofNat 12809246696557140246 => return .op .natBeq
  | .ofNat 17049977161890552712 => return .boolTrue
  | .ofNat 12846390003443303075 => return .nat
  | .ofNat 14613595360914645637 => return .op .natPow
  | .ofNat 7893555430612621797 => return .bool
  | .ofNat 14735850464179338479 => return .natZero
  | .ofNat 5082277153363671981 => return .op .natMul
  | .ofNat 16195091492847522412 => return .boolFalse
  | .ofNat 6836287016865057964 => return .op .natSucc
  | .ofNat 14029550093476971811 => return .op .natAdd
  | _ => none
def allowedAxiom : F → Bool
  | .ofNat 0x18831fc8d02adfac589f6943dd3ae1e1b75b313456b70ec510123cd79030dcfb => true
  | .ofNat 0x13d6e2f59015a84d4b63e9aed1b27df52578b65bca8acb079e80b7f1f3af3b0a => true
  | .ofNat 0x1fd43f4fb0e31d0923596b27713089d7777a57b5bb49194970154dd9e5eb9634 => true
  | .ofNat 0x37ddd82901fb45241cf6ec55dd3ee9fcb449d4698e838d5d53d1e4cf096a251f => true
  | .ofNat 0x2816fe85294ab4d31429248de49a2d8f8ce04cb2d768505afb4b04e508d1c9f5 => true
  | _ => false
def allowedAxiomQuick : F → Bool
  | .ofNat 11763543932651680745 => true
  | .ofNat 5663773883625405697 => true
  | .ofNat 13106183114281513418 => true
  | .ofNat 456940176556830579 => true
  | .ofNat 10304962820087913574 => true
  | _ => false
--PIN

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
