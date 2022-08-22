import LSpec
import Yatima.Typechecker.Eval
import TestsUtils.CompileAndExtractTests

open Yatima LSpec

open Typechecker

def readBackNeutral : Neutral → Expr
  | .fvar name idx _ => .var name idx
  | .const name idx univs => .const name idx univs

local instance : Coe (Except ε α) (Option α) where coe
  | .ok a => some a
  | .error _ => none

partial def shiftCtx (ctx : Context) : Context :=
  -- NOTE: these gets could be very expensive, is there a way to avoid or optimize? Like some sort of WHNF of thunked values?
  ctx.withExprs $ ctx.exprs.map fun val => match val.get with
    | .app (.fvar name idx typ) args => Value.app (.fvar name (idx + 1) typ) args
    | other => other

mutual
  /--
    Replace free variables in `e` with values from `ctx.exprs`.
  -/
  partial def replaceFvars (consts : Array Const) (ctx : Context) (e : Expr) : Option Expr :=
    let replace expr := replaceFvars consts ctx expr
    match e with
      | .var _ idx => readBack consts (ctx.exprs.get! idx).get
      | .app fn e  => do pure $ .app (← replace fn) (← replace e)
      | .lam n bin t b => do
        let lamCtx := shiftCtx ctx
        let lamCtx := lamCtx.extendWith
          -- TODO double-check ordering here
          $ Value.app (.fvar n 0 $ Value.sort .zero) []
        pure $ .lam n bin (← replace t) (← replaceFvars consts lamCtx b)
      | .letE n e t b  => do pure $ .letE n (← replace e) (← replace t) (← replace b)
      | .proj n e  => do pure $ .proj n (← replace e)
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
    | .sort univ => pure $ .sort univ
    | .app neu args => args.foldlM (init := readBackNeutral neu) fun acc arg => do
      pure $ Expr.app acc $ ← readBack consts arg.get
    | .lam name binfo bod env => do
      -- any neutral fvars in the environment are now additionally nested,
      -- and so must have their de bruijn indices incremented
      let lamCtx := shiftCtx env
      let lamCtx := lamCtx.extendWith
        -- binder types are irrelevant to reduction and so are lost on evaluation;
        -- arbitrarily fill these in with `Sort 0`
        -- TODO double-check ordering here
        $ Value.app (.fvar name 0 $ Value.sort .zero) []
      pure $ .lam name binfo (.sort .zero) $ ← replaceFvars consts lamCtx bod
    | .pi name binfo dom bod ctx => do
      let piCtx := shiftCtx ctx
      let piCtx := piCtx.extendWith
        -- TODO double-check ordering here
        $ Value.app (.fvar name 0 dom) []
      pure $ .lam name binfo (← readBack consts dom.get) $ ← replaceFvars consts piCtx bod
    | .lit lit => pure $ .lit lit
    -- TODO need to look into this case in the typechecker to make sure this is correct
    | .proj idx neu vals => vals.foldlM (init := readBackNeutral neu) fun expr val =>
      return .app expr (← readBack consts val.get)
    | .lty l => pure $ .lty l
    | .exception _ => none
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
        let some (.definition const) ← pure state.consts[idx]? | throw "invalid definition index"
        let some (.definition rconst) ← pure state.consts[ridx]? | throw "invalid definition index"
        match TypecheckM.run (.init state.consts) $ eval const.value with
        | .ok value =>
          dbg_trace s!"READBACK ------------------------------------------------------------------------------------------"
          let some expr ← pure $ readBack state.consts value | throw "failed to read back value"
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
  | .lam n bin _ b => .lam n bin (.sort .zero) (stripBinderTypes b)
  | .pi n bin _ b => .pi n bin (.sort .zero) (stripBinderTypes b)
  | .app fn e  => .app (stripBinderTypes fn) (stripBinderTypes e)
  | .letE n e t b  => .letE n (stripBinderTypes e) (stripBinderTypes t) (stripBinderTypes b)
  | .proj n e  => .proj n (stripBinderTypes e)
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
      -- (`A, `A'),
      -- (`B, `B'),
      -- (`C, `C'),
      -- (`D, `D'),
      -- (`E, `E'),
      -- (`F, `F'),
      (`G, `G')
    ]

def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Typechecker/Reduction.lean"
    [tcExtractor]
  lspecIO tSeq
