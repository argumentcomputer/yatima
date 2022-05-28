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
  | lam _ _ _ body => 1 + numBinders body
  | pi _ _ _ body => 1 + numBinders body
  | _ => 0

-- Shift the de Bruijn of all bound variables at depth > `dep`.  
def shift (expr : Expr) (inc : Nat) (dep : Option Nat := none) : Expr := match expr with
  | var name idx                => match dep with
    | some dep => if idx < dep then var name idx else var name <| idx + inc
    | none     => var name <| idx + inc
  | app func input              => app (func.shift inc dep) (input.shift inc dep)
  | lam name bind type body     => lam name bind type (body.shift inc <| dep.map .succ)
  | pi name bind type body      => pi name bind type (body.shift inc <| dep.map .succ)
  | letE name type value body =>  
    letE name type value (body.shift inc <| dep.map .succ)
  | fix name body               => fix name <| body.shift inc dep
  | other                       => other -- All the rest of the cases are treated at once

/-
TODO1: Fill in the `Fix` sorry after some guidance
TODO2: I'm not sure this is right because I'm copying my work for untyped λ calculus which is 
probably way simpler

Substitute the expression `input` for any bound variable with de Bruijn index `subDep`
-/
def subst (expr input : Expr) (subDep : Nat := 0) : Expr :=
shiftBack $ substAux expr input subDep
where 
substAux (expr input : Expr) (subDep : Nat := 0) : Expr := match expr with 
  | var name idx => if idx == subDep then input else var name idx
  | app func input' => app (substAux func input subDep) (substAux input' input subDep) 
  | lam name bind type body => 
    lam name bind (type.substAux input subDep) (body.substAux (.shift input 1 <| pure 0) subDep.succ) 
  | pi name bind type body => 
    pi name bind (type.substAux input subDep.succ) (body.substAux (.shift input 1 <| pure 0) subDep.succ) 
  | letE name type value body => 
    letE name (type.substAux input subDep) (value.substAux input subDep) (body.substAux (.shift input 1 <| pure 0) subDep.succ) 
  | fix name body => sorry
  | expr => expr -- All the rest of the cases are treated at once
-- Shifts the dB indices of the outer-most Lambda by 1, this is separate because shift above only takes `Nat` input
shiftBack : Expr → Expr 
  | var name idx => match idx with
    | 0          => unreachable! -- all the `0`-idx variables should be substituted out
    | .succ idx' => var name idx'
  | app func input' => app (shiftBack func) (shiftBack input')
  | letE name type value body => letE name (shiftBack type) (shiftBack value) (shiftBack body)
  | fix name body => sorry
  | other => other
end Expr

end Yatima