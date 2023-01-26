import YatimaStdLib.NonEmpty

-- Based on https://nbviewer.org/github/grin-compiler/grin/blob/master/papers/boquist.pdf
namespace Grin

/-- Var represents a variable binding, such as in a function definition in a pattern -/
structure Var where
  data : Lean.FVarId
/-- Id represents a known definition, such as a function or constructor -/
structure Id where
  data : Lean.FVarId

inductive Tag where
-- Suspended full applications
| F : Id → Tag
-- Partial applications
| P : Id → Nat → Tag
-- Saturated constructors
| C : Id → Tag

inductive Literal
  | str : String → Literal
  | num : Nat → Literal

inductive SVal where
  | lit : Literal → SVal
  | var : Var → SVal

inductive Val where
  | ctag  : Tag → List SVal → Val
  | cvar  : Var → List SVal → Val
  | stag  : Tag → Val
  | empty : Val
  | sval  : SVal → Val

inductive CPat where
  -- Complete tag pattern
  | ctag : Tag → List Var → CPat
  -- Single tag pattern
  | stag : Tag → CPat
  | lit  : Literal → CPat

abbrev LPat := Val

inductive SExpr where
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
  | unit : Val → Expr
  | seq  : SExpr → LPat → Expr → Expr
  | case : Val → NEList (CPat × Expr) → Expr
  | «if» : Val → Expr → Expr → Expr

structure Binding where
  defn : Var
  args : NEList Var
  body : Expr

abbrev Prog := NEList Binding 

end Grin
