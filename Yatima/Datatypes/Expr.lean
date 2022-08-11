import Yatima.Datatypes.Univ

namespace Yatima

inductive BinderInfo
  | default
  | implicit
  | strictImplicit
  | instImplicit
  | auxDecl
  deriving BEq, Inhabited

inductive LitType
  | nat : LitType
  | str : LitType
  deriving BEq, Inhabited

inductive Literal
  | nat : Nat → Literal
  | str : String → Literal
  deriving BEq, Inhabited

namespace Ipld

abbrev Nat?ᵣ k := Split Unit (Option Nat) k

abbrev BinderInfoₗ k := Split BinderInfo Unit k

inductive Expr (k : Kind)
  | var   : Nameᵣ k → LNat k → Nat?ᵣ k → List (UnivCid k) → Expr k
  | sort  : UnivCid k → Expr k
  | const : Nameᵣ k → ConstCid k → List (UnivCid k) → Expr k
  | app   : ExprCid k → ExprCid k → Expr k
  | lam   : Nameᵣ k → BinderInfoₗ k → ExprCid k → ExprCid k → Expr k
  | pi    : Nameᵣ k → BinderInfoₗ k → ExprCid k → ExprCid k → Expr k
  | letE  : Nameᵣ k → ExprCid k → ExprCid k → ExprCid k → Expr k
  | lit   : Split Literal Unit k → Expr k
  | lty   : Split LitType Unit k → Expr k
  | proj  : LNat k → ExprCid k → Expr k
  deriving BEq, Inhabited

def Expr.ctoNameᵣ : Expr k → String
  | .var   .. => "var"
  | .sort  .. => "sort"
  | .const .. => "const"
  | .app   .. => "app"
  | .lam   .. => "lam"
  | .pi    .. => "pi"
  | .letE  .. => "let"
  | .lit   .. => "lit"
  | .lty   .. => "lty"
  | .proj  .. => "proj"

end Ipld

abbrev ConstIdx := Nat

inductive Expr
  | var   : Name → Nat → Expr
  | sort  : Univ → Expr
  | const : Name → ConstIdx → List Univ → Expr
  | app   : Expr → Expr → Expr
  | lam   : Name → BinderInfo → Expr → Expr → Expr
  | pi    : Name → BinderInfo → Expr → Expr → Expr
  | letE  : Name → Expr → Expr → Expr → Expr
  | lit   : Literal → Expr
  | lty   : LitType → Expr
  | proj  : Nat → Expr → Expr
  deriving Inhabited, BEq

namespace Expr

def name : Expr → Option Name
  | var   n _
  | const n ..
  | lam   n ..
  | pi    n ..
  | letE  n .. => some n
  | _ => none

def bInfo : Expr → Option BinderInfo
  | lam _ b ..
  | pi  _ b .. => some b
  | _ => none

def type : Expr → Option (Expr)
  | lam _ _ t _ => some t
  | pi _ _ t _ => some t
  | letE _ t _ _ => some t
  | _ => none

def body : Expr → Option (Expr)
  | lam  _ _ _ b
  | pi   _ _ _ b
  | letE _ _ _ b => some b
  | _ => none

def isVarFree (name : Name) : Expr → Bool
  | var name' _ => name == name'
  | app func input => isVarFree name func || isVarFree name input
  | lam name' _ type body => isVarFree name type || (name != name' && isVarFree name body)
  | pi name' _ type body => isVarFree name type || (name != name' && isVarFree name body)
  | letE name' type value body => isVarFree name type || isVarFree name value || (name != name' && isVarFree name body)
  | proj _ body => isVarFree name body
  | _ => false

-- Get the list of de Bruijn indices of all the variables of a Yatima `Expr` (helpful for debugging later)
def getIndices : Expr → List Nat
  | var _ idx => [idx]
  | app func input => getIndices func ++ getIndices input
  | lam _ _ type body => getIndices type ++ getIndices body
  | pi _ _ type body => getIndices type ++ getIndices body
  | letE _ type value body => getIndices type ++ getIndices value ++ getIndices body
  | proj _ body => getIndices body
  | _ => [] -- All the rest of the cases are treated at once

def getBVars : Expr → List Name
  | var name _ => [name]
  | app func input => getBVars func ++ getBVars input
  | lam _ _ type body => getBVars type ++ getBVars body
  | pi _ _ type body => getBVars type ++ getBVars body
  | letE _ type value body => getBVars type ++ getBVars value ++ getBVars body
  | proj _ body => getBVars body
  | _ => [] -- All the rest of the cases are treated at once

def ctorType : Expr → String
  | var   .. => "var"
  | sort  .. => "sort"
  | const .. => "const"
  | app   .. => "app"
  | lam   .. => "lam"
  | pi    .. => "pi"
  | letE  .. => "let"
  | lit   .. => "lit"
  | lty   .. => "lty"
  | proj  .. => "proj"

-- Gets the depth of a Yatima Expr (helpful for debugging later)
def numBinders : Expr → Nat
  | lam  _ _ _ body
  | pi   _ _ _ body
  | letE _ _ _ body => 1 + numBinders body
  | _ => 0

/--
Shift the de Bruijn indices of all variables at depth > `cutoff` in expression `expr` by an increment `inc`.

`shiftFreeVars` and `subst` implementations are variation on those for untyped λ-expressions from `ExprGen.lean`.
-/
def shiftFreeVars (expr : Expr) (inc : Int) (cutoff : Nat) : Expr :=
  let rec walk (cutoff : Nat) (expr : Expr) : Expr := match expr with
    | var name idx => match inc with
      | .ofNat inc   => if idx < cutoff then var name idx else var name <| idx + inc
      | .negSucc inc => if idx < cutoff then var name idx else var name <| idx - inc.succ -- 0 - 1 = 0
    | app func input            => app (walk cutoff func) (walk cutoff input)
    | lam name bind type body   => lam name bind (walk cutoff type) (walk cutoff.succ body)
    | pi name bind type body    => pi name bind (walk cutoff type) (walk cutoff.succ body)
    | letE name type value body =>
      letE name (walk cutoff type) (walk cutoff value) (walk cutoff.succ body)
    | other                     => other -- All the rest of the cases are treated at once
  walk cutoff expr

/--
Shift the de Bruijn indices of all variables in expression `expr` by increment `inc`.
-/
def shiftVars (expr : Expr) (inc : Int) : Expr :=
  let rec walk (expr : Expr) : Expr := match expr with
    | var name idx              =>
      let idx : Nat := idx
      match inc with
        | .ofNat inc   => var name <| idx + inc
        | .negSucc inc => var name <| idx - inc.succ -- 0 - 1 = 0
    | app func input            => app (walk func) (walk input)
    | lam name bind type body   => lam name bind (walk type) (walk body)
    | pi name bind type body    => pi name bind (walk type) (walk body)
    | letE name type value body =>
      letE name (walk type) (walk value) (walk body)
    | other                     => other -- All the rest of the cases are treated at once
  walk expr

/--
Substitute the expression `term` for any bound variable with de Bruijn index
`dep` in the expression `expr`
-/
def subst (expr term : Expr) (dep : Nat) : Expr :=
  let rec walk (acc : Nat) : Expr → Expr
    | var name idx => match compare idx (dep + acc) with
      | .eq => term.shiftFreeVars acc 0
      | .gt => var name (idx - 1)
      | .lt => var name idx
    | app func input => app (walk acc func) (walk acc input)
    | lam name bind type body =>
      lam name bind (walk acc type) (walk acc.succ body)
    | pi name bind type body =>
      pi name bind (walk acc type) (walk acc.succ body)
    | letE name type value body =>
      letE name (walk acc type) (walk acc value) (walk acc.succ body)
    | other => other -- All the rest of the cases are treated at once
  walk 0 expr

/--
Substitute the expression `term` for the top level bound variable of the
expression `expr`.

(essentially just `(λ. M) N` )
-/
def substTop (expr term : Expr) : Expr :=
  expr.subst (term.shiftFreeVars 1 0) 0 |>.shiftFreeVars (-1) 0

end Expr

end Yatima
