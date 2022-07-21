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

  partial def exprToLurkExpr (expr : Expr) : TranslateM Lurk.Expr :=
    match expr with
    | _ => sorry

  partial def constToLurkExpr (const : Const) : TranslateM $ Option Lurk.Expr :=
    match const with
    | .axiom    _
    | .quotient _ => return none
    | .theorem  _ => return some (.lit .t)
    | .opaque   x => do
      match (← read).expr_cache.find? x.value with
      | some expr => exprToLurkExpr expr
      | none      => throw "a"
    | .definition x => do
      match (← read).expr_cache.find? x.value with
      | some expr => exprToLurkExpr expr
      | none      => throw "a"
    | _ => sorry

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
