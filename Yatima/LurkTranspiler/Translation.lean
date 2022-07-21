import Yatima.Store
import Yatima.ForLurkRepo.Printer

open Yatima

abbrev State := Array (String × Lurk.Expr)

abbrev TranslateM := ReaderT Store $ EStateM String State

/--
Takes an array of bindings in reverse order outputs a `Lurk.letE`.

Suppose that we have A and B such that B depends on A. `bindings` will be
`#[(B, β), (A, α)]` where `β` and `α` are the expressions of `B` and `A`
respectively.

The reverse order was chosen for optimization reasons, since we expect to
recursively backtrack on dependencies often.
-/
def compileBindings (bindings : State) : Lurk.Expr := sorry

def TranslateM.run (store : Store) (ste : State) (m : TranslateM α) :
    Except String String :=
  match EStateM.run (ReaderT.run m store) ste with
  | .ok _ ste  => .ok (compileBindings ste).print
  | .error e _ => .error e

mutual

  -- Maybe useful later:
  -- partial def telescopeApp (expr : Expr) : TranslateM $ Lurk.Expr := 
  --   sorry 

  -- partial def telescopeLam (expr : Expr) : TranslateM Lurk.Expr := 
  --   sorry 
  
  partial def exprToLurkExpr (expr : Expr) : TranslateM $ Option Lurk.Expr :=
    match expr with 
    | .var name i     => return some $ .lit (.sym name)
    | .sort  ..       => return none
    | .const name ..  => return some $ .lit (.sym name)
    | .app fn arg => do 
      let fn ← exprToLurkExpr fn
      let arg ← exprToLurkExpr arg 
      match fn, arg with 
      -- TODO: this is extremely bad lol, need to flatten
      | some f, some a => return some $ .app f [a]
      |      _,      _ => throw ""
    | .lam name _ _ body => do
      match ← exprToLurkExpr body with 
      -- TODO: this is extremely bad lol, need to flatten
      | some body => return some $ .lam [name] body
      |         _ => throw ""
    -- TODO: Do we erase?
    | .pi    .. => sorry
    -- TODO
    | .letE  .. => sorry
    | .lit lit  => match lit with 
      -- TODO: need to include `Int` somehow
      | .nat n => return some $ .lit (.num n)
      | .str s => return some $ .lit (.str s)
    | .lty   .. => return none
    | .fix _ e  => exprToLurkExpr e
    -- TODO
    | .proj  .. => sorry

  partial def constToLurkExpr (const : Const) : TranslateM $ Option Lurk.Expr :=
    match const with
    | .axiom    _
    | .quotient _ => return none
    | .theorem  _ => return some (.lit .t)
    | .opaque   x => do
      match (← read).expr_cache.find? x.value with
      | some expr => exprToLurkExpr expr
      | none      => throw s!"opaque {x.name} not found"
    | .definition x => do
      match (← read).expr_cache.find? x.value with
      | some expr => exprToLurkExpr expr
      | none      => throw s!"definition {x.name} not found"
    /-
    I feel like we shouldn't compile the projections.
    We should ignore the projections and compile everything 
    when we hit the mutual block instead. That way we get 
    all the mutuals at once and there's no cyclic
    weirdness in this recursion.
    -/
    | .inductiveProj ind
    | .constructorProj ctor
    | .recursorProj recr   
    | .definitionProj defn  => return none
    -- TODO
    | .mutDefBlock dss => sorry 
    | .mutIndBlock thms => sorry 

end

/-- Main translation function. The dependency order is reversed. -/
def translateM : TranslateM Unit := do
  let store ← read
  store.const_cache.forM fun _ const => do
    match ← constToLurkExpr const with
    | some expr => set $ #[(const.name, expr)].append (← get)
    | none      => pure ()

def translate (store : Store) : Except String String :=
  TranslateM.run store #[] (translateM store)
