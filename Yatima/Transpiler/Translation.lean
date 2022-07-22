import Yatima.Store
import Yatima.Transpiler.TranspileM
import Yatima.ForLurkRepo.Printer

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
    -- Note: we replace `.` with `:` since `.` is a special character in Lurk
    | .var name i     => return some $ .lit (.sym $ name.replace "." ":")
    | .const name ..  =>
      -- TODO: I think this is where we should call `.append` on `State`
      return some $ .lit (.sym $ name.replace "." ":")
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
    | .pi    .. => sorry
    -- TODO
    | .letE  .. => sorry
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
    | .opaque   x => do
      match (← read).expr_cache.find? x.value with
      | some expr => exprToLurkExpr expr
      | none      => throw s!"opaque '{x.name}' not found"
    | .definition x => do
      match (← read).expr_cache.find? x.value with
      | some expr => exprToLurkExpr expr
      | none      => throw s!"definition '{x.name}' not found"
    -- TODO
    | .mutDefBlock dss  => sorry 
    | .mutIndBlock inds => sorry 

end

/-- Main translation function. The dependency order is reversed. -/
def transpileM : TranspileM Unit := do
  let store ← read
  store.const_cache.forM fun _ const => do
    match ← constToLurkExpr const with
    | some expr => set $ #[(const.name, expr)].append (← get)
    | none      => pure ()

def transpile (store : Store) : Except String String :=
  match TranspileM.run store #[] (transpileM store) with
  | .ok  ste => return ste.compile.print
  | .error e => throw e

end Yatima.Transpiler
