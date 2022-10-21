import LSpec
import Yatima.Typechecker.Eval
import TestsUtils.CompileAndExtractTests

open Yatima LSpec TC Typechecker

local instance : Coe (Except ε α) (Option α) where coe
  | .ok a => some a
  | .error _ => none

partial def shiftEnv (env : Env) : Env :=
  -- NOTE: these gets could be very expensive, is there a way to avoid or optimize? Like some sort of WHNF of thunked values?
  env.withExprs $ env.exprs.map fun val => match val.get with
    | .app (.fvar name idx) args => .mk default (Value.app (.fvar name (idx + 1)) args)
    | _ => val

mutual
  /--
    Replace free variables in `e` with values from `env.exprs`.
  -/
  partial def replaceFvars (consts : Array Const) (env : Env) (e : TypedExpr) : Option TypedExpr :=
    let replace expr := replaceFvars consts env expr
    match e with
    | .var _ _ idx => readBack consts (env.exprs.get! idx).get
    | .app _ fn e  => return .app default (← replace fn) (← replace e)
    | .lam _ n bin ty b => do
      let lamEnv := shiftEnv env
      let lamEnv := lamEnv.extendWith
        -- TODO double-check ordering here
        $ .mk default $ Value.app (.fvar n 0) []
      return .lam default n bin (← replace ty) (← replaceFvars consts lamEnv b)
    | .letE _ n e ty b  => return .letE default n (← replace e) (← replace ty) (← replace b)
    | .proj _ s n e  => return .proj default s n (← replace e)
    | e => pure e

  /--
    Convert a `Value` back into its `Expr` representation.
    We use this function to test by converting the reduced `Value` expression back into an `Expr`,
    enabling us to compare this to the exected reduced expression.

    This is preferrable to comparing value-to-value because the latter requires
    one of the following:
    - Build the expected `Value` from scratch. This would be very inconvenient to have to do for every test.
    - Reduce the expected expression to a `Value` and compare. This is fragile because we're using the very function
      we're testing as part of the testing infractructure. E.g. a bug that causes
      all expressions to reduce to the same thing would make everything pass.
  -/
  partial def readBack (consts : Array Const) : Value → Option TypedExpr
    | .sort univ => pure $ .sort default univ
    | .app neu args => do args.foldlM (init := ← readBackNeutral consts neu) fun acc arg => do
      pure $ TypedExpr.app default acc $ ← readBack consts arg.get
    | .lam name binfo dom bod env => do
      -- any neutral fvars in the environment are now additionally nested,
      -- and so must have their de bruijn indices incremented
      let lamEnv := shiftEnv env
      let lamEnv := lamEnv.extendWith
        -- binder types are irrelevant to reduction and so are lost on evaluation;
        -- arbitrarily fill these in with `Sort 0`
        -- TODO double-check ordering here
        $ .mk default $ Value.app (.fvar name 0) []
      pure $ .lam default name binfo (← readBack consts dom.get) $ ← replaceFvars consts lamEnv bod
    | .pi name binfo dom bod env => do
      let piEnv := shiftEnv env
      let piEnv := piEnv.extendWith
        -- TODO double-check ordering here
        $ .mk default $  Value.app (.fvar name 0) []
      pure $ .lam default name binfo (← readBack consts dom.get) $ ← replaceFvars consts piEnv bod
    | .lit lit => pure $ .lit default lit
    | .litProp _ => none -- FIXME
    | .exception _ => none

  partial def readBackNeutral (consts : Array Const) : Neutral → Option TypedExpr
    | .fvar name idx => pure $ .var default name idx
    | .const name idx univs => pure $ .const default name idx univs
    | .proj s idx val => do
      let val ← readBack consts val.value
      pure $ .proj default s idx val

end

def getConstPairs (state : Compiler.CompileState) (consts : List (Name × Name)) :
    Except String (Array ((Name × TypedExpr) × (Name × TypedExpr))) := do
  let mut pairList := #[]
  let mut notFound := #[]
  for (constName, rconstName) in consts do
    match state.cache.find? constName with
    | none            => notFound := notFound.push constName
    | some (_, idx) =>
      match state.cache.find? rconstName with
      | none            => notFound := notFound.push rconstName
      | some (_, ridx)  =>
        let some (.definition const) ← pure state.tcStore.consts[idx]? | throw "invalid definition index"
        let some (.definition rconst) ← pure state.tcStore.consts[ridx]? | throw "invalid definition index"
        match TypecheckM.run (.init state.tcStore) (.init state.tcStore) do eval (← infer const.value).1, TypecheckM.run (.init state.tcStore) (.init state.tcStore) do pure (← infer rconst.value).1 with
        | .ok value, .ok rexpr =>
          -- dbg_trace s!"READBACK ------------------------------------------------------------------------------------------"
          let some expr ← pure $ readBack state.tcStore.consts value | throw s!"failed to read back value {value}"
          pairList := pairList.push ((constName, expr), (rconstName, rexpr))
        | _, _ => .error "failed to evaluate value"
  if notFound.isEmpty then
    return pairList
  else
    throw s!"Not found: {", ".intercalate (notFound.data.map toString)}"

def makeTcTests (pairs : Array ((Name × TypedExpr) × (Name × TypedExpr))) : TestSeq :=
  pairs.foldl (init := .done) fun tSeq ((nameReduced, constReduced), (nameExpected, constExpected)) =>
    tSeq ++ test s!"Comparing {nameReduced} to {nameExpected}:\n  Reduced:\t{constReduced}\n  Expected:\t{constExpected}"
      (constReduced == constExpected)

def extractTcTests := fun pairs stt =>
  withExceptOk "All constants can be found" (getConstPairs stt pairs)
    makeTcTests

def tcExtractor := extractTcTests [
    (`A, `A'),
    (`B, `B'),
    (`C, `C'),
    (`D, `D'),
    (`E, `E'),
    (`F, `F'),
    (`G, `G'),
    (`H, `H'),
    (`I, `I'),
    (`J, `J'),
    (`K, `K'),
    (`L, `L')
  ]

def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Typechecker/Reduction.lean"
    [extractIpldTests, tcExtractor]
  lspecIO tSeq
