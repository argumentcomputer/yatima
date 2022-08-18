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
    | .app (.fvar name idx typ) args => ⟨fun _ => .app (.fvar name (idx + 1) typ) args⟩
    | other => other

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
      ⟨fun _ => .app (.fvar name 0 ⟨fun _ => .sort .zero⟩) []⟩
    let evalBod ← eval bod |>.run (.initCtx lamCtx consts)
    pure $ .lam name binfo (.sort .zero) $ ← readBack consts evalBod
  | .pi name binfo dom bod ctx => do
    let piCtx := shiftCtx ctx
    let piCtx := piCtx.extendWith
      -- TODO double-check ordering here
      ⟨fun _ => .app (.fvar name 0 dom) []⟩
    let evalBod ← eval bod  |>.run (.initCtx piCtx consts)
    pure $ .lam name binfo (← readBack consts dom.get) $ ← readBack consts evalBod
  | .lit lit => pure $ .lit lit
  -- TODO need to look into this case in the typechecker to make sure this is correct
  | .proj idx neu vals => vals.foldlM (init := readBackNeutral neu) fun expr val =>
    return .app expr (← readBack consts val.get)
  | .lty l => pure $ .lty l
  | .exception _ => none

def getConstPairs (state : Compiler.CompileState) (consts : List (Name × Name)) :
    Except String (List ((Name × Expr) × (Name × Expr))) := do
  let mut pairList := []
  let mut notFound := []
  for (constName, rconstName) in consts do
    match state.cache.find? constName with
    | none            => notFound := constName :: notFound
    | some (_, idx) =>
      match state.cache.find? rconstName with
      | none            => notFound := rconstName :: notFound
      | some (_, ridx)  =>
        let some (.definition const) ← pure state.consts[idx]? | throw "invalid definition index"
        let some (.definition rconst) ← pure state.consts[ridx]? | throw "invalid definition index"
        match TypecheckM.run (.init state.consts) $ eval const.value with
        | .ok value =>
          let some expr ← pure $ readBack state.consts value | throw "failed to read back value"
          pairList := ((constName, expr), (rconstName, rconst.value)) :: pairList
        | _ => .error "failed to evaluate value"
  if notFound.isEmpty then
    return pairList.reverse
  else
    throw s!"Not found: {", ".intercalate (notFound.map toString)}"

def makeTcTests (pairList : List ((Name × Expr) × (Name × Expr))) :
    TestSeq :=
  pairList.foldl (init := .done) fun tSeq ((nameReduced, constReduced), (nameExpected, constExpected)) =>
    tSeq ++ test s!"Comparing {nameReduced} to {nameExpected}:\n  Reduced:\t{constReduced}\n  Expected:\t{constExpected}" (constReduced == constExpected)

def extractTcTests := fun stt state =>
  withExceptOk "All constants can be found" (getConstPairs state stt)
  fun constPairs => makeTcTests constPairs

def tcExtractor := extractTcTests
    [(`A, `A'),
     (`B, `B'),
     (`C, `C'),
     (`D, `D'),
     (`E, `E'),
     (`F, `F'),
     (`G, `G')
    ]

def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Typechecker/Reduction.lean"
    [tcExtractor]
  lspecIO tSeq
