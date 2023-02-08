import Yatima.Compiler.GrinM
import Lean.Expr
open Lean.Compiler.LCNF

def Lean.FVarId.toVar (id : Lean.FVarId) : Yatima.Grin.Var := .mk id.name

namespace Yatima.Grin

def mkFreshVar : GrinM Var := do
  pure ⟨← Lean.mkFreshId⟩

def paramsToVars (params : Array Param) : List Var :=
  params.toList.map (fun param => param.fvarId.toVar)

def fetch? (id : Lean.FVarId) : GrinM SExpr := do
  match ← varKind id with
  | .pointer => pure $ .fetch id.toVar .none
  | .basic => pure $ .unit $ .sval $ .var id.toVar

mutual
partial def PScheme : Alt → GrinM (CPat × Expr)
| .default code => do
  let expr ← RScheme code
  pure (.default, expr)
| .alt ctor params code  => do
  let args := paramsToVars params
  let tag := .C ⟨ ctor ⟩
  let expr ← RScheme code
  pure (.ctag tag args, expr)

partial def RScheme : Code → GrinM Expr
| .let decl k => match decl.value with
  | .erased => RScheme k
  | .value val => do
    let op := .unit $ .sval $ .lit val
    let pat := sorry
    let expr ← RScheme k
    pure $ .seq op pat expr
  | .proj _ idx struct => do
    let op := sorry
    let pat := sorry
    let expr ← RScheme k
    pure $ .seq op pat expr
  | .const name _ args => do
    let op := sorry
    let pat := sorry
    let expr ← RScheme k
    pure $ .seq op pat expr
  | .fvar var args => do
    let op := sorry
    let pat := sorry
    let expr ← RScheme k
    pure $ .seq op pat expr
| .cases case => do
  -- Since every variable is initially strict, we don't need to eval before
  let new_var ← mkFreshVar
  let caseVal := .sval $ .var new_var
  let some patExprs := NEList.nonEmpty (← case.alts.toList.mapM PScheme)
    | throw "Empty pattern"
  let caseExpr := .case caseVal patExprs
  pure $ .seq (← fetch? case.discr) (.svar new_var) caseExpr
  -- pure expr
| .return fvarId => do
  -- In the lazy case, a return is a call to eval, but since we chose strict semantics this
  -- will either be a `fetch` or `unit` instruction depending on whether the variable is a
  -- pointer or basic value
  pure $ .ret $ ← fetch? fvarId
| .fun _decl _k => throw "Should not find function definition here (?)"
-- We need to figure out a way to implement join points
| .jp _decl _k => throw "TODO"
| .jmp _fvarId _args => throw "TODO"
| .unreach _type => throw "Unreach found"
end

def compileDeclaration (decl : Decl) : GrinM Binding := do
  let defn := ⟨decl.name⟩
  let args := paramsToVars decl.params
  let body ← RScheme decl.value
  let binding := { defn, args, body }
  pure binding

end Yatima.Grin
