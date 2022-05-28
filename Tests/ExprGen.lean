/-
This file will define tests related to Yatima `Expr`s. In particular, to test `shift` and `subst` 
the aim is to write a generator for random `Expr` trees.

For now all it does is generate untyped lambda expressions, but this is just a PoC for the main goal.
-/
import Yatima.Expr

-- Basic inductive type for lambda expressions to test the expression generator before trying it on
-- full blown Yatima Exprs
inductive lExpr
  | var : Nat → lExpr
  | lam : lExpr → lExpr
  | app : lExpr → lExpr → lExpr
deriving Inhabited

namespace lExpr

-- Positive shifts only
def shift (inc : Nat) (cutoff : Nat) : lExpr → lExpr
  | var idx        => if idx < cutoff then var idx else var $ inc + idx
  | lam body       => lam $ body.shift inc <| cutoff.succ
  | app func input => app (func.shift inc cutoff) (input.shift inc cutoff)

-- Substitution for lambda expressions
def subst (expr term : lExpr) (dep : Nat) : lExpr := 
shiftBack $ substAux expr term dep
where 
substAux expr term dep : lExpr := match expr with
  | var idx => if idx == dep then term else var idx
  | lam body => lam $ body.subst (term.shift 1 0) (dep + 1)
  | app func body => app (func.subst term dep) (body.subst term dep)
shiftBack expr : lExpr := match expr with
  | var idx => match idx with
    | 0 => unreachable! -- All the `0`-idx variables should be substituted out
    | idx' + 1 => var idx'
  | lam body => lam body
  | app func input => app (shiftBack func) (shiftBack input)

end lExpr