import Lean.Expr
import Lean.Compiler.LCNF
import YatimaStdLib.NonEmpty

open Lean.Compiler.LCNF

-- Based on https://nbviewer.org/github/grin-compiler/grin/blob/master/papers/boquist.pdf
namespace Yatima.Grin

/-- Var represents a variable binding, such as in a function definition in a pattern -/
structure Var where
  data : Lean.Name
/-- Id represents a known definition, such as a function or constructor -/
structure Id where
  data : Lean.Name
/-- VarKind tells us whether a variable is a pointer or a basic value -/
inductive VarKind
| pointer
| basic

inductive Tag where
-- Suspended full applications
| F : Id → Tag
-- Partial applications
| P : Id → Nat → Tag
-- Saturated constructors
| C : Id → Tag

abbrev Literal := LitValue

inductive SVal where
  | lit : Literal → SVal
  | var : Var → SVal

inductive Val where
  | ctag  : Tag → List SVal → Val
  | stag  : Tag → Val
  | empty : Val
  | sval  : SVal → Val

inductive CPat where
  -- Complete tag pattern
  | ctag : Tag → List Var → CPat
  -- Single tag pattern
  | stag : Tag → CPat
  | lit  : Literal → CPat

inductive LPat where
  | ctag  : Tag → List SVal → LPat
  | cvar  : Var → List SVal → LPat
  | stag  : Tag → LPat
  | svar  : Var → LPat

inductive SExpr where
  | unit   : Val → SExpr
  | store  : Val → SExpr
  | fetch  : Var → Option Nat → SExpr
  | update : Var → Val → SExpr
  -- Known function call
  | call   : Id → NEList SVal → SExpr
  -- Evaluation of unknown expression
  | eval   : Var → SExpr
  -- Application of unknown function to a list of arguments
  | apply  : Var → NEList SVal → SExpr

inductive Expr where
  | ret  : SExpr → Expr
  | seq  : SExpr → LPat → Expr → Expr
  | join : Expr → LPat → Expr → Expr
  | case : Val → NEList (CPat × Expr) → Expr

structure Binding where
  defn : Id
  args : List Var
  body : Expr

abbrev Prog := NEList Binding

end Yatima.Grin
