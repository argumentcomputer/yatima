import Yatima.Typechecker.Datatypes
import Std.Data.RBMap

/-!
# The Typechecker monad

This module defines the typechecker monad `TypecheckM`, together with various utilities to run and
initialize its context.
-/

namespace Yatima.Typechecker

open IR
open Lurk (F)

abbrev RecrCtx    := Std.RBMap Nat (F × List TypedValue × TypedExpr) compare
abbrev ConstNames := Std.RBMap F Lean.Name compare
abbrev Store      := Std.RBMap F Const compare

/--
The context available to the typechecker monad. The available fields are
* `lvl : Nat` : Depth of the subterm. Coincides with the length of the list of types
* `env : Env` : A environment of known values, and universe levels. See `Env`
* `types : List TypedValue` : The types of the values in `Env`.
* `store : Store` : An store of known constants in the context.
-/
structure TypecheckCtx where
  lvl         : Nat
  env         : Env
  types       : List TypedValue
  store       : Store
  /-- Maps a variable index (which represents a reference to a mutual const)
    to the hash of that constant (in `TypecheckState.typedConsts`) and
    a function returning a `TypedValue` for that constant's type given a list of universes. -/
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
  typedConsts : Std.RBMap F TypedConst compare
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
`val : TypedValue`, `typ : TypedValue` pair.

The `lvl` of the `TypecheckCtx` is also incremented.
TODO: Get clarification on this.
-/
def withExtendedCtx (val typ : TypedValue) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with
    lvl := ctx.lvl + 1,
    types := typ :: ctx.types,
    env := ctx.env.extendWith val }

/--
Evaluates a `TypecheckM` computation with a `TypecheckCtx` with a the environment extended by a
`val : TypedValue` (whose type is not known, unlike `withExtendedCtx`)
-/
def withExtendedEnv (val : TypedValue) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with env := ctx.env.extendWith val }

/--
Evaluates a `TypecheckM` computation with a `TypecheckCtx` whose environment is an extension of `env`
by a `val : TypedValue`
-/
def withNewExtendedEnv (env : Env) (val : TypedValue) :
    TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with env := env.extendWith val }

def withLimitedAxioms : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with limitAxioms := true }

def withRecF (f : F) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with recF? := some f }

def withDbg : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with dbg := true }

def tc_trace (msg : String) : TypecheckM Unit := do
  if (← read).dbg then dbg_trace msg

--PIN
def primToF : PrimConst → Option F
  | .op .natBlt => return .ofNat 0x30bdcaed7817048a737ef863f5109bc2389ae7be528f0e90d41960fa730acfaf
  | .op .natBle => return .ofNat 0x00b87cb52650564edd64c02a175169b05878b385dc5faeac171c79db114630d6
  | .string => return .ofNat 0x2c495d690af6582f289013adaa7ce0fbd0bd3dcb4df4ea7ff9e4551007ee77bc
  | .op .natBeq => return .ofNat 0x2f1fc68611f113692e0940beb639ff42294801b26818524679f155a9f80a5afd
  | .boolTrue => return .ofNat 0x3d618e3f3c3e82bb16123ca6ddb11811d8783231372eb35717c2fbab68ec2ec7
  | .nat => return .ofNat 0x107cf99c15125e9e7238b80bb98445b9879ac53174055644a1ddd7407e99012e
  | .op .natPow => return .ofNat 0x2ea6b4fad0378be16344acabf5336027eeab05ee9f04f412d0d8a2b333af1b00
  | .bool => return .ofNat 0x2fb6590a8abb53f510d78a62c25cfc5522f361af31df2d85a3dc754efacd9c13
  | .natZero => return .ofNat 0x372f729d31dfb4fd194c65625ee86054be71cf88d390abb738c45ca88fe9b10e
  | .op .natMul => return .ofNat 0x091c78654da740eb9760e20178a09c58aeb194ce57472ef8e6e6d28b422d2dbc
  | .boolFalse => return .ofNat 0x2ff24cbb3da368d0a0900d88543f2af03693315a9c10fcb3eb11575353562723
  | .op .natSucc => return .ofNat 0x1b3cb7740979e391dbb3dab5430497d1f88838b6bab6aa057634cccc44b6675d
  | .op .natAdd => return .ofNat 0x30b44e981f80898378de952ee7d55e3ce0ecbf5cb4faa6983d32e74c43a75479
def fToPrim : F → Option PrimConst
  | .ofNat 0x30bdcaed7817048a737ef863f5109bc2389ae7be528f0e90d41960fa730acfaf => return .op .natBlt
  | .ofNat 0x00b87cb52650564edd64c02a175169b05878b385dc5faeac171c79db114630d6 => return .op .natBle
  | .ofNat 0x2c495d690af6582f289013adaa7ce0fbd0bd3dcb4df4ea7ff9e4551007ee77bc => return .string
  | .ofNat 0x2f1fc68611f113692e0940beb639ff42294801b26818524679f155a9f80a5afd => return .op .natBeq
  | .ofNat 0x3d618e3f3c3e82bb16123ca6ddb11811d8783231372eb35717c2fbab68ec2ec7 => return .boolTrue
  | .ofNat 0x107cf99c15125e9e7238b80bb98445b9879ac53174055644a1ddd7407e99012e => return .nat
  | .ofNat 0x2ea6b4fad0378be16344acabf5336027eeab05ee9f04f412d0d8a2b333af1b00 => return .op .natPow
  | .ofNat 0x2fb6590a8abb53f510d78a62c25cfc5522f361af31df2d85a3dc754efacd9c13 => return .bool
  | .ofNat 0x372f729d31dfb4fd194c65625ee86054be71cf88d390abb738c45ca88fe9b10e => return .natZero
  | .ofNat 0x091c78654da740eb9760e20178a09c58aeb194ce57472ef8e6e6d28b422d2dbc => return .op .natMul
  | .ofNat 0x2ff24cbb3da368d0a0900d88543f2af03693315a9c10fcb3eb11575353562723 => return .boolFalse
  | .ofNat 0x1b3cb7740979e391dbb3dab5430497d1f88838b6bab6aa057634cccc44b6675d => return .op .natSucc
  | .ofNat 0x30b44e981f80898378de952ee7d55e3ce0ecbf5cb4faa6983d32e74c43a75479 => return .op .natAdd
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
  | .ofNat 0x38dd8c1780c323d861748b8926022f54b73c0d7ac1c0ef37d5eb9ab5f224f534 => true
  | .ofNat 0x211958c49b62d3061ffd08018456abadc661a7e629dbe19b05cb26baca9e00dc => true
  | .ofNat 0x27554fd1fd3db9231c0bdf8099d6ca7283c124c599fd67e39dd049532eb667b4 => true
  | .ofNat 0x1b0f0369765b9f8e3a7e8711ac188d88be12a4113d70f160879954e82d8d7fdc => true
  | .ofNat 0x275f3bc2007a5bbc052d39a29731c0fd3ef5da817e65dd299683f9fcf6ab5e16 => true
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
  op : Array TypedValue → TypecheckM (Option Value)

def PrimConstOp.toPrimOp : PrimConstOp → PrimOp
  | .natSucc => .mk fun vs => do
    let some v := vs.get? 0
      | throw "At least one TypedValue element needed for PrimConstOp.natSucc"
    match v.body with
    | .lit (.natVal v) => pure $ .some $ .lit (.natVal v.succ)
    | _ => pure none
  | .natAdd => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two TypedValue elements needed for PrimConstOp.natAdd"
    match v.body, v'.body with
    | .lit (.natVal v), .lit (.natVal v') => pure $ .some $ .lit (.natVal (v+v'))
    | _, _ => pure none
  | .natMul => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two TypedValue elements needed for PrimConstOp.natMul"
    match v.body, v'.body with
    | .lit (.natVal v), .lit (.natVal v') => pure $ .some $ .lit (.natVal (v*v'))
    | _, _ => pure none
  | .natPow => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two TypedValue elements needed for PrimConstOp.natPow"
    match v.body, v'.body with
    | .lit (.natVal v), .lit (.natVal v') => pure $ .some $ .lit (.natVal (Nat.pow v v'))
    | _, _ => pure none
  | .natBeq => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two TypedValue elements needed for PrimConstOp.natBeq"
    match v.body, v'.body with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v = v' then do
        pure $ some $ .neu (.const (← primF .boolTrue) [])
      else do
        pure $ some $ .neu (.const (← primF .boolFalse) [])
    | _, _ => pure none
  | .natBle => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two TypedValue elements needed for PrimConstOp.natBle"
    match v.body, v'.body with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v ≤ v' then do
        pure $ some $ .neu (.const (← primF .boolTrue) [])
      else do
        pure $ some $ .neu (.const (← primF .boolFalse) [])
    | _, _ => pure none
  | .natBlt => .mk fun vs => do
    let some (v, v') := do pure (← vs.get? 0, ← vs.get? 1)
      | throw "At least two TypedValue elements needed for PrimConstOp.natBlt"
    match v.body, v'.body with
    | .lit (.natVal v), .lit (.natVal v') =>
      if v < v' then do
        pure $ some $ .neu (.const (← primF .boolTrue) [])
      else do
        pure $ some $ .neu (.const (← primF .boolFalse) [])
    | _, _ => pure none

end Yatima.Typechecker
