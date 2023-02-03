import Yatima.Compiler.GrinM

open Lean.Compiler.LCNF

namespace Yatima.Grin

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
| .cases _cases => throw "TODO"
| .return fvarId => do
  -- In the lazy case, a return is a call to eval, but since we chose strict semantics this
  -- will either be a `fetch` or `unit` instruction depending on whether the variable is a
  -- pointer or basic value
  match ← varKind fvarId with
  | .pointer => pure $ .ret $ .fetch ⟨fvarId⟩ .none
  | .basic => pure $ .ret $ .unit $ .sval $ .var ⟨fvarId⟩
| .fun _decl _k => throw "Should not happen (?)"
-- We need to figure out a way to implement join points
| .jp _decl _k => throw "TODO"
| .jmp _fvarId _args => throw "TODO"
| .unreach _type => throw "Should not happen"

def compileDeclaration (decl : Decl) : GrinM Binding := do
  let defn := ⟨decl.name⟩
  let args := decl.params.toList.map (fun param => Var.mk param.fvarId)
  let body ← RScheme decl.value
  let binding := { defn, args, body }
  pure binding

end Yatima.Grin
