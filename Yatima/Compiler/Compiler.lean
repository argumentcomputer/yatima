import Yatima.Compiler.GrinM
import Lean.Expr
open Lean.Compiler.LCNF

def Lean.FVarId.toVar (id : Lean.FVarId) : Yatima.Grin.Var := .mk id.name

namespace Yatima.Grin

def mkFreshVar : GrinM Var := do
  pure ⟨← Lean.mkFreshId⟩

def fetch? (id : Lean.FVarId) : GrinM SExpr := do
  match ← varKind id with
  | .pointer => pure $ .fetch id.toVar .none
  | .basic => pure $ .unit $ .sval $ .var id.toVar

def PScheme : Alt → GrinM Expr :=
  sorry

def RScheme : Code → GrinM Expr
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
  let expr := .seq (← fetch? case.discr) (.svar new_var) sorry
  -- let val := .sval $ .var ⟨cases.discr⟩
  -- let nelistPatExpr := sorry
  -- pure $ .case val nelistPatExpr
  pure expr
| .return fvarId => do
  -- In the lazy case, a return is a call to eval, but since we chose strict semantics this
  -- will either be a `fetch` or `unit` instruction depending on whether the variable is a
  -- pointer or basic value
  pure $ .ret $ ← fetch? fvarId
| .fun _decl _k => throw "Should not happen (?)"
-- We need to figure out a way to implement join points
| .jp _decl _k => throw "TODO"
| .jmp _fvarId _args => throw "TODO"
| .unreach _type => throw "Should not happen"

def compileDeclaration (decl : Decl) : GrinM Binding := do
  let defn := ⟨decl.name⟩
  let args := decl.params.toList.map (fun param => param.fvarId.toVar)
  let body ← RScheme decl.value
  let binding := { defn, args, body }
  pure binding

end Yatima.Grin
