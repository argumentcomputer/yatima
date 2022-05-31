import Yatima.Env
import Yatima.Univ

namespace Yatima

  inductive Bind
  | default
  | implicit
  | strictImplicit
  | instImplicit
  deriving BEq, Inhabited

  inductive LitType
  | nat : LitType
  | str : LitType
  deriving BEq, Inhabited

  inductive Literal
  | nat : Nat → Literal
  | str : String → Literal
  deriving BEq, Inhabited

  inductive Expr
  | var   : Name → Nat → Expr
  | sort  : Univ → Expr
  | const : Name → ConstCid → List Univ → Expr
  | app   : Expr → Expr → Expr
  | lam   : Name → Bind → Expr → Expr → Expr
  | pi    : Name → Bind → Expr → Expr → Expr
  | letE  : Name → Expr → Expr → Expr → Expr
  | lit   : Literal → Expr
  | lty   : LitType → Expr
  | fix   : Name → Expr → Expr
  deriving BEq, Inhabited

  inductive ExprAnon
  | var   : Nat → ExprAnon
  | sort  : UnivAnonCid → ExprAnon
  | const : ConstAnonCid → List UnivAnonCid → ExprAnon
  | app   : ExprAnonCid → ExprAnonCid → ExprAnon
  | lam   : Bind → ExprAnonCid → ExprAnonCid → ExprAnon
  | pi    : Bind → ExprAnonCid → ExprAnonCid → ExprAnon
  | letE  : ExprAnonCid → ExprAnonCid → ExprAnonCid → ExprAnon
  | lit   : Literal → ExprAnon
  | lty   : LitType → ExprAnon
  | fix   : ExprAnonCid → ExprAnon
  deriving BEq, Inhabited

  inductive ExprMeta
  | var   : Name → ExprMeta
  | sort  : UnivMetaCid → ExprMeta
  | const : Name → ConstMetaCid → List UnivMetaCid → ExprMeta
  | app   : ExprMetaCid → ExprMetaCid → ExprMeta
  | lam   : Name → ExprMetaCid → ExprMetaCid → ExprMeta
  | pi    : Name → ExprMetaCid → ExprMetaCid → ExprMeta
  | letE  : ExprMetaCid → ExprMetaCid → ExprMetaCid → ExprMeta
  | lit   : ExprMeta
  | lty   : ExprMeta
  | fix   : Name → ExprMetaCid → ExprMeta
  deriving BEq, Inhabited

namespace Expr

-- Get the list of de Bruijn indices of all the variables of a Yatima `Expr` (helpful for debugging later)
def getIndices : Expr → List Nat
  | var _ idx => [idx]
  | app func input => getIndices func ++ getIndices input
  | lam _ _ type body => getIndices type ++ getIndices body
  | pi _ _ type body => getIndices type ++ getIndices body
  | letE _ type value body => getIndices type ++ getIndices value ++ getIndices body
  | fix _ body => getIndices body
  | _ => [] -- All the rest of the cases are treated at once

-- Gets the depth of a Yatima Expr (helpful for debugging later)
def numBinders : Expr → Nat
  | lam _ _ _ body  => 1 + numBinders body
  | pi _ _ _ body   => 1 + numBinders body
  | letE _ _ _ body => 1 + numBinders body
  | fix _ body      => 1 + numBinders body
  | _ => 0

/--
Shift the de Bruijn indices of all bound variables at depth > `dep`.

`shift` and `subst` implementations are variation on those for untyped λ-expressions from `Tests/ExprGen.lean`.
-/
def shift (expr : Expr) (inc : Int) (cutoff : Nat) : Expr := 
  let rec walk (cutoff : Nat) (expr : Expr) : Expr := match expr with
    | var name idx              => 
      match inc with
        | .ofNat inc   => if idx < cutoff then var name idx else var name <| idx + inc
        | .negSucc inc => if idx < cutoff then var name idx else var name <| idx - inc.succ -- 0 - 1 = 0 
    | app func input            => app (walk cutoff func) (walk cutoff input)
    | lam name bind type body   => lam name bind (walk cutoff type) (walk cutoff.succ body)
    | pi name bind type body    => pi name bind (walk cutoff type) (walk cutoff.succ body)
    | letE name type value body =>
      letE name (walk cutoff type) (walk cutoff value) (walk cutoff.succ body)
    | fix name body             => fix name (walk cutoff.succ body)
    | other                     => other -- All the rest of the cases are treated at once
  walk cutoff expr
/--
Substitute the expression `term` for any bound variable with de Bruijn index `subDep`
-/
def subst (expr term : Expr) (dep : Nat) : Expr :=
  let rec walk (acc : Nat) (expr : Expr) : Expr := match expr with
    | var name idx => if idx == dep + acc then term.shift acc 0 else var name idx
    | app func input => app (walk acc func) (walk acc input) 
    | lam name bind type body => 
      lam name bind (walk acc type) (walk acc.succ body) 
    | pi name bind type body => 
      pi name bind (walk acc type) (walk acc.succ body) 
    | letE name type value body => 
      letE name (walk acc type) (walk acc value) (walk acc.succ body) 
    | fix name body => fix name (walk acc.succ body) 
    | other => other -- All the rest of the cases are treated at once
  walk 0 expr

/--
Substitute the expression `term` for the top level bound variable of the expression `expr`. 

(essentially just `(λ. M) N` )
-/
def substTop (expr term : Expr) : Expr :=
  expr.subst (term.shift 1 0) 0 |>.shift (-1) 0

end Expr

end Yatima