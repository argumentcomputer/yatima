import Lurk.Backend.DSL
import Lurk.Backend.ExprUtils

namespace Lurk.Backend.Expr
-- open Lurk.Frontend AST Macro DSL

/-- This is a super dangerous instance, because of how tricky names are;
  I'm just gonna turn it on for now, but may cause terrible bugs. -/
instance (priority := low) : ToExpr Lean.Name where
  toExpr name := .sym name.toString

def mkApp (f : Expr) (args : List Expr) : Expr :=
  args.foldl (init := f) fun acc e => .app acc e

end Lurk.Backend.Expr