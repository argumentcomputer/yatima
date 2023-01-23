import YatimaStdLib.NonEmpty

-- Based on https://nbviewer.org/github/grin-compiler/grin/blob/master/papers/boquist.pdf
namespace Grin

abbrev Var := String
abbrev Id := String

inductive Tag where
-- Suspended full applications
| F : Id → Tag
-- Partial applications
| P : Id → Tag
-- Saturated constructors
| C : Id → Tag

inductive SVal where
  | str : String → SVal
  | num : Nat → SVal
  | var : Var → SVal

inductive Val where
  | ctag : Tag → List SVal → Val
  | cvar : Var → List SVal → Val
  | stag : Tag → Val
  | empty : Val
  | sval : SVal → Val

inductive CPat where
  | ctag : Tag → List Var → CPat
  | stag : Tag → CPat
  | str : String → CPat
  | num : Nat → CPat

abbrev LPat := Val

mutual
inductive Expr where
  | seq : SExpr → LPat → Expr → Expr
  | case : Val → NEList (CPat × Expr) → Expr
  | «if» : Val → Expr → Expr → Expr
  | op : SExpr → Expr

inductive SExpr where
  | app : Var → NEList SVal → SExpr
  | unit : Val → SExpr
  | store : Val → SExpr
  | fetch : Var → Option Nat → SExpr
  | update : Var → Val → SExpr
  | expr : Expr → SExpr
end

structure Binding where
  defn : Var
  args : NEList Var
  body : Expr
  

abbrev Prog := NEList Binding 

end Grin
