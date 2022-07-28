import LSpec
import Yatima.Compiler.Compiler
import Yatima.Ipld.FromIpld
import YatimaStdLib.List
import Yatima.Typechecker.Eval

open Yatima

def readBack (value : Typechecker.Value) : Expr := sorry

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
            | .ok value => pairList := (readBack value, rconst.value) :: pairList
            | _ => return .error "failed to evaluate value"
    if notFound.isEmpty then
      return .ok pairList
    else
      return .error s!"Not found: {", ".intercalate (notFound.map toString)}"

def makeTests (pairList : List (Expr × Expr)) :
    TestSeq :=
  pairList.foldl (init := .done) fun tSeq (constCompiled, constConverted) =>
    tSeq ++ test s!"{constCompiled.name} compiled = {constConverted.name} converted" (constCompiled == constConverted)
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
  lspecEachWith allPairs generateTestSeq
