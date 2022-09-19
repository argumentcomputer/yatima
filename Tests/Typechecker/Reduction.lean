import LSpec
import Yatima.Typechecker.Eval
import TestsUtils.CompileAndExtractTests

open Yatima LSpec

open Typechecker

local instance : Coe (Except ε α) (Option α) where coe
  | .ok a => some a
  | .error _ => none

partial def shiftEnv (env : Env) : Env :=
  -- NOTE: these gets could be very expensive, is there a way to avoid or optimize? Like some sort of WHNF of thunked values?
  env.withExprs $ env.exprs.map fun val => match val.get with
    | .app (.fvar name idx) args => Value.app (.fvar name (idx + 1)) args
    | other => other

mutual
  /--
    Replace free variables in `e` with values from `env.exprs`.
  -/
  partial def replaceFvars (consts : Array Const) (env : Env) (e : Expr) : Option Expr :=
    let replace expr := replaceFvars consts env expr
    match e with
    | .var _ _ idx => readBack consts (env.exprs.get! idx).get
    | .app _ fn e  => return .app default (← replace fn) (← replace e)
    | .lam _ n bin ty b => do
      let lamEnv := shiftEnv env
      let lamEnv := lamEnv.extendWith
        -- TODO double-check ordering here
        $ Value.app (.fvar n 0) []
      return .lam default n bin (← replace ty) (← replaceFvars consts lamEnv b)
    | .letE _ n e ty b  => return .letE default n (← replace e) (← replace ty) (← replace b)
    | .proj _ n e  => return .proj default n (← replace e)
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
  partial def readBack (consts : Array Const) : Value → Option Expr
    | .sort univ => pure $ .sort default univ
    | .app neu args => do args.foldlM (init := ← readBackNeutral consts neu) fun acc arg => do
      pure $ Expr.app default acc $ ← readBack consts arg.get
    | .lam name binfo bod env => do
      -- any neutral fvars in the environment are now additionally nested,
      -- and so must have their de bruijn indices incremented
      let lamEnv := shiftEnv env
      let lamEnv := lamEnv.extendWith
        -- binder types are irrelevant to reduction and so are lost on evaluation;
        -- arbitrarily fill these in with `Sort 0`
        -- TODO double-check ordering here
        $ Value.app (.fvar name 0) []
      pure $ .lam default name binfo (.sort default .zero) $ ← replaceFvars consts lamEnv bod
    | .pi name binfo dom bod env => do
      let piEnv := shiftEnv env
      let piEnv := piEnv.extendWith
        -- TODO double-check ordering here
        $ Value.app (.fvar name 0) []
      pure $ .lam default name binfo (← readBack consts dom.get) $ ← replaceFvars consts piEnv bod
    | .lit lit => pure $ .lit default lit
    | .exception _ => none

  partial def readBackNeutral (consts : Array Const) : Neutral → Option Expr
    | .fvar name idx => pure $ .var default name idx
    | .const name idx univs => pure $ .const default name idx univs
    | .proj idx val => do
      let val ← readBack consts val
      pure $ .proj default idx val

end

def getConstPairs (state : Compiler.CompileState) (consts : List (Name × Name)) :
    Except String (Array ((Name × Expr) × (Name × Expr))) := do
  let mut pairList := #[]
  let mut notFound := #[]
  for (constName, rconstName) in consts do
    match state.cache.find? constName with
    | none            => notFound := notFound.push constName
    | some (_, idx) =>
      match state.cache.find? rconstName with
      | none            => notFound := notFound.push rconstName
      | some (_, ridx)  =>
        let some (.definition const) ← pure state.pStore.consts[idx]? | throw "invalid definition index"
        let some (.definition rconst) ← pure state.pStore.consts[ridx]? | throw "invalid definition index"
        match TypecheckM.run (.init state.pStore) $ eval const.value with
        | .ok value =>
          -- dbg_trace s!"READBACK ------------------------------------------------------------------------------------------"
          let some expr ← pure $ readBack state.pStore.consts value | throw s!"failed to read back value {value}"
          pairList := pairList.push ((constName, expr), (rconstName, rconst.value))
        | _ => .error "failed to evaluate value"
  if notFound.isEmpty then
    return pairList
  else
    throw s!"Not found: {", ".intercalate (notFound.data.map toString)}"

/--
Strip the binder types from lambdas in `e` (i.e., replace them with `Sort 0`) for the purpose of comparison.
-/
def stripBinderTypes : Expr → Expr
  | .lam _ n bin _ b => .lam default n bin (.sort default .zero) (stripBinderTypes b)
  | .pi _ n bin _ b => .pi default n bin (.sort default .zero) (stripBinderTypes b)
  | .app _ fn e  => .app default (stripBinderTypes fn) (stripBinderTypes e)
  | .letE _ n e ty b  => .letE default n (stripBinderTypes e) (stripBinderTypes ty) (stripBinderTypes b)
  | .proj _ n e  => .proj default n (stripBinderTypes e)
  | e => e

def makeTcTests (pairs : Array ((Name × Expr) × (Name × Expr))) : TestSeq :=
  pairs.foldl (init := .done) fun tSeq ((nameReduced, constReduced), (nameExpected, constExpected)) =>
    let constExpected := stripBinderTypes constExpected
    tSeq ++ test s!"Comparing {nameReduced} to {nameExpected}:\n  Reduced:\t{constReduced}\n  Expected:\t{constExpected}"
      (constReduced == constExpected)

def extractTcTests := fun pairs stt =>
  withExceptOk "All constants can be found" (getConstPairs stt pairs)
    makeTcTests

def tcExtractor := extractTcTests
    [
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
    [tcExtractor]
  lspecIO tSeq
