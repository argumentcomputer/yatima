import Yatima.Univ

namespace Yatima

def Name? (k : Kind) := UnitIfAnon k Name

inductive LitType
  | nat : LitType
  | str : LitType
  deriving BEq, Inhabited

inductive Literal
  | nat : Nat → Literal
  | str : String → Literal
  deriving BEq, Inhabited

inductive BinderInfo
  | default
  | implicit
  | strictImplicit
  | instImplicit
  | auxDecl
  deriving BEq, Inhabited

inductive Expr (k : Kind)
  | var   : Name? k → UnitIfMeta k Nat → Expr k
  | sort  : UnivCid k → Expr k
  | const : Name? k → ConstCid k → List (UnivCid k) → Expr k
  | app   : Expr k → Expr k → Expr k
  | lam   : Name? k → UnitIfMeta k BinderInfo → Expr k → Expr k → Expr k
  | pi    : Name? k → UnitIfMeta k BinderInfo → Expr k → Expr k → Expr k
  | letE  : Name? k → Expr k → Expr k → Expr k → Expr k
  | lit   : UnitIfMeta k Literal → Expr k
  | lty   : UnitIfMeta k LitType → Expr k
  | fix   : Name? k → Expr k → Expr k
  | proj  : UnitIfMeta k Nat → Expr k → Expr k
  -- deriving BEq, Inhabited

namespace Expr

def name : Expr .Pure → Option Name
  | lam name .. => some name
  | pi name .. => some name
  | letE name .. => some name
  | _ => none

def bInfo : Expr .Pure → Option BinderInfo
  | lam _ b _ _ => some b
  | pi _ b _ _ => some b
  | _ => none

def type : Expr .Pure → Option (Expr .Pure)
  | lam _ _ t _ => some t
  | pi _ _ t _ => some t
  | letE _ t _ _ => some t
  | _ => none

def body : Expr .Pure → Option (Expr .Pure)
  | lam _ _ _ b => some b
  | pi _ _ _ b => some b
  | letE _ _ _ b => some b
  | _ => none

-- Get the list of de Bruijn indices of all the variables of a Yatima `Expr` (helpful for debugging later)
def getIndices : Expr .Pure → List Nat
  | var _ idx => [idx]
  | app func input => getIndices func ++ getIndices input
  | lam _ _ type body => getIndices type ++ getIndices body
  | pi _ _ type body => getIndices type ++ getIndices body
  | letE _ type value body => getIndices type ++ getIndices value ++ getIndices body
  | fix _ body => getIndices body
  | proj _ body => getIndices body
  | _ => [] -- All the rest of the cases are treated at once

def getBVars : Expr .Pure → List Name
  | var name _ => [name]
  | app func input => getBVars func ++ getBVars input
  | lam _ _ type body => getBVars type ++ getBVars body
  | pi _ _ type body => getBVars type ++ getBVars body
  | letE _ type value body => getBVars type ++ getBVars value ++ getBVars body
  | fix _ body => getBVars body
  | proj _ body => getBVars body
  | _ => [] -- All the rest of the cases are treated at once

def ctorType : Expr .Pure → String
  | var .. => "var"
  | sort .. => "sort"
  | const .. => "const"
  | app .. => "app"
  | lam .. => "lam"
  | pi .. => "pi"
  | letE .. => "let"
  | lit .. => "lit"
  | lty .. => "lty"
  | fix .. => "fix"
  | proj .. => "proj"

-- Gets the depth of a Yatima Expr (helpful for debugging later)
def numBinders : Expr .Pure → Nat
  | lam _ _ _ body  => 1 + numBinders body
  | pi _ _ _ body   => 1 + numBinders body
  | letE _ _ _ body => 1 + numBinders body
  | fix _ body      => 1 + numBinders body
  | _ => 0

/--
Shift the de Bruijn indices of all variables at depth > `cutoff` in expression `expr` by an increment `inc`.

`shiftFreeVars` and `subst` implementations are variation on those for untyped λ-expressions from `ExprGen.lean`.
-/
def shiftFreeVars (expr : Expr .Pure) (inc : Int) (cutoff : Nat) : Expr .Pure :=
  let rec walk (cutoff : Nat) (expr : Expr .Pure) : Expr .Pure := match expr with
    | var name idx              =>
      let idx : Nat := idx
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
Shift the de Bruijn indices of all variables in expression `expr` by increment `inc`.
-/
def shiftVars (expr : Expr .Pure) (inc : Int) : Expr .Pure :=
  let rec walk (expr : Expr .Pure) : Expr .Pure := match expr with
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
    | fix name body             => fix name (walk body)
    | other                     => other -- All the rest of the cases are treated at once
  walk expr

/--
Substitute the expression `term` for any bound variable with de Bruijn index `dep` in the expression `expr`
-/
def subst (expr term : Expr .Pure) (dep : Nat) : Expr .Pure :=
  let rec walk (acc : Nat) (expr : Expr .Pure) : Expr .Pure := match expr with
    | var name idx => let idx : Nat := idx
      match compare idx (dep + acc) with
        | .eq => term.shiftFreeVars acc 0
        | .gt => let pred : Nat := idx - 1
          var name pred
        | .lt => var name idx
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
def substTop (expr term : Expr .Pure) : Expr .Pure :=
  expr.subst (term.shiftFreeVars 1 0) 0 |>.shiftFreeVars (-1) 0

end Expr

end Yatima
