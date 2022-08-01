import LSpec
import Yatima.Compiler.Compiler
import YatimaStdLib.List
import Yatima.Typechecker.Eval

open Yatima LSpec

open Typechecker (Value)

def readBackNeutral : Typechecker.Neutral → Expr
  | .fvar name idx _ => .var name idx
  | .const name idx univs => .const name idx univs

partial def shiftEnv (env : Typechecker.Env Value) : Typechecker.Env Value :=
  -- NOTE: these gets could be very expensive, is there a way to avoid or optimize? Like some sort of WHNF of thunked values?
  { env with exprs := env.exprs.map fun val => match val.get with
    | .app (.fvar name idx typ) args => ⟨fun _ => .app (.fvar name (idx + 1) typ) args⟩
    | other => other
  }

partial def readBack (defns : Array Const) : Value → Option Expr
  | .sort univ => pure $ .sort univ
  | .app neu args => args.foldlM (init := readBackNeutral neu) fun acc arg => do
    pure $ Expr.app acc $ ← readBack defns arg.get
  | .lam name binfo bod env => do
    -- any neutral fvars in the environment are now additionally nested,
    -- and so must have their de bruijn indices incremented
    let lamEnv := shiftEnv env
    let lamEnv := { lamEnv with
      -- binder types are irrelevant to reduction and so are lost on evaluation;
      -- arbitrarily fill these in with `Sort 0`
      -- TODO double-check ordering here
      exprs := ⟨fun _ => Value.app (.fvar name 0 ⟨fun _ => .sort .zero⟩) []⟩ :: lamEnv.exprs
    }
    let evalBod ← (match Typechecker.eval bod  |>.run (.initEnv lamEnv defns) with
      | .ok val => some val
      | .error _ => none
    )
    pure $ .lam name binfo (.sort .zero) $ ← readBack defns evalBod
  | .pi name binfo dom bod env => do
    let piEnv := shiftEnv env
    let piEnv := { piEnv with
      -- TODO double-check ordering here
      exprs := ⟨fun _ => Value.app (.fvar name 0 dom) []⟩ :: piEnv.exprs
    }
    let evalBod ← (match Typechecker.eval bod  |>.run (.initEnv piEnv defns) with
      | .ok val => some val
      | .error _ => none
    )
    pure $ .lam name binfo (← readBack defns dom.get) $ ← readBack defns evalBod
  | .lit lit => pure $ .lit lit
  | .lty lty => pure $ .lty lty
  -- TODO need to look into this case in the typechecker to make sure this is correct
  | .proj idx neu vals => vals.foldlM (init := readBackNeutral neu) fun expr val => do pure $ .app expr (← readBack defns val.get)

def getConstPairs (fileName : String) (consts : List (Lean.Name × Lean.Name)) :
    IO $ Except String (List (Expr × Expr)) := do
  match ← Compiler.compile fileName with
  | .error msg => return .error (toString msg)
  | .ok state =>
    let mut pairList : List (Expr × Expr) := []
    let mut notFound : List Lean.Name := []
    for (constName, rconstName) in consts do
      match state.cache.find? constName with
      | none            => notFound := constName :: notFound
      | some (_, idx) =>
        match state.cache.find? rconstName with
        | none            => notFound := rconstName :: notFound
        | some (_, ridx)  =>
          let some (.definition const) ← pure state.defns[idx]? | return .error "invalid definition index"
          let some (.definition rconst) ← pure state.defns[ridx]? | return .error "invalid definition index"
          match Typechecker.TypecheckM.run (.init state.defns) $ Typechecker.eval const.value with
            | .ok value =>
              let some expr ← pure $ readBack state.defns value | return .error "failed to read back value"
              pairList := (expr, rconst.value) :: pairList
            | _ => return .error "failed to evaluate value"
    if notFound.isEmpty then
      return .ok pairList
    else
      return .error s!"Not found: {", ".intercalate (notFound.map toString)}"

def makeTests (pairList : List (Expr × Expr)) :
    TestSeq :=
  pairList.foldl (init := .done) fun tSeq (constCompiled, constConverted) =>
    tSeq ++ test s!"{constCompiled} (reduced) = {constConverted} (expected)" (constCompiled == constConverted)
def reductionPairs :=
  ("Fixtures/Typechecker/Reduction.lean",
    [(`A, `A'),
     (`B, `B')]
  )
def allPairs : List (String × List (Lean.Name × Lean.Name)) := [ reductionPairs ]

def generateTestSeq (x : String × List (Lean.Name × Lean.Name)) : IO TestSeq :=
  return withExceptOk s!"Compiles '{x.1}'" (← getConstPairs x.1 x.2)
    fun pairs => makeTests pairs

def main : IO UInt32 := do
  Compiler.setLibsPaths
  lspecEachIO allPairs generateTestSeq
