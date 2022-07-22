import Yatima.Store
import Yatima.Transpiler.TranspileM
import Yatima.ForLurkRepo.Printing

/-- We replace `.` with `:` since `.` is a special character in Lurk -/
def String.fixDot (s : String) : String :=
  s.replace "." ":"

namespace Yatima.Transpiler

open Yatima

mutual

  -- Maybe useful later:
  -- partial def telescopeApp (expr : Expr) : TranspileM $ Lurk.Expr := 
  --   sorry 

  -- partial def telescopeLam (expr : Expr) : TranspileM Lurk.Expr := 
  --   sorry 
  
  partial def exprToLurkExpr : Expr → TranspileM (Option Lurk.Expr)
    | .sort  ..
    | .lty   .. => return none
    | .var name i     => return some $ .lit (.sym $ name.fixDot)
    | .const name cid ..  => do 
      let visited? := (← get).visited.contains name
      if !visited? then 
        visit name -- cache
        let const? := (← read).const_cache.find? cid
        match const? with 
        | some const => 
          -- The binding works here because `constToLurkExpr`
          -- will recursively process its children.
          -- Hence we know that this binding will always come after
          -- all of its children have already been bound 
          match ← constToLurkExpr const with 
          | some expr => appendBinding (name.fixDot, expr) 
          | none => pure ()
        | none => throw s!"constant '{name}' not found"
      return some $ .lit (.sym $ name.fixDot)
    | .app fn arg => do 
      let fn ← exprToLurkExpr fn
      let arg ← exprToLurkExpr arg 
      match fn, arg with 
      -- TODO: flatten
      | some f, some a => return some $ .app f [a]
      | _,      _      => throw "TODO"
    | .lam name _ _ body => do
      match ← exprToLurkExpr body with 
      -- TODO: flatten
      | some body => return some $ .lam [name] body
      | _         => throw "TODO"
    -- TODO: Do we erase?
    -- MP: I think we erase
    | .pi    .. => return some $ .lit .nil
    -- TODO
    | .letE name _ value body  => do
      match (← exprToLurkExpr value), (← exprToLurkExpr body) with
        | some val, some body => return some $ .letE [(name, val)] body
        | _, _ => throw "TODO"
    | .lit lit  => match lit with 
      -- TODO: need to include `Int` somehow
      | .nat n => return some $ .lit (.num n)
      | .str s => return some $ .lit (.str s)
    | .fix _ e => exprToLurkExpr e
    -- TODO
    | .proj  .. => sorry

  /--
  We're trying to compile the mutual blocks at once instead of compiling each
  projection separately to avoid some recursions.

  Arthur: I think there are some complications with mutual blocks for inductives
  because of recursors and constructors. We need to make sure we won't translate
  the same block more than once.
  -/
  partial def constToLurkExpr : Const → TranspileM (Option Lurk.Expr)
    | .inductiveProj   _
    | .constructorProj _
    | .recursorProj    _   
    | .definitionProj  _
    | .axiom           _
    | .quotient        _ => return none
    | .theorem  _ => return some (.lit .t)
    | .opaque   x => do match (← read).expr_cache.find? x.value with
      | some expr => exprToLurkExpr expr
      | none      => throw s!"opaque '{x.name}' not found"
    | .definition x => do match (← read).expr_cache.find? x.value with
      | some expr => exprToLurkExpr expr
      | none      => throw s!"definition '{x.name}' not found"
    -- TODO
    | .mutDefBlock dss  => sorry 
    | .mutIndBlock inds => sorry 

end

/--
Main translation function. The generated dependency order is reversed.

Suppose that we have A and B such that B depends on A. `bindings` will be
`#[(B, β), (A, α)]` where `β` and `α` are the expressions of `B` and `A`
respectively.

The reverse order was chosen for optimization reasons, since we expect to
recursively backtrack on dependencies often and appending on arrays is faster
than prepending.
-/
def transpileM : TranspileM Unit := do
  let store ← read
  store.const_cache.forM fun _ const => do
    match ← constToLurkExpr const with
    | some expr => appendBinding (const.name.fixDot, expr)
    | none      => pure ()

/-- Constructs the array of bindings and builds a `Lurk.Expr.letE` from it. -/
def transpile (store : Store) : Except String String :=
  match TranspileM.run store ⟨#[], .empty⟩ (transpileM store) with
  | .ok ⟨bindings, _⟩ =>
    let expr : Lurk.Expr := .letE bindings.reverse.data .currEnv
    return expr.print
  | .error e => throw e

end Yatima.Transpiler
