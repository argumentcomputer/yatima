import Yatima.Datatypes.Univ

namespace Yatima

namespace IR

-- Carries a `Lean.Name` for meta
scoped notation "Nameₘ" => Split Unit Name

-- Carries a `Nat` for anon
scoped notation "Natₐ" => Split Nat Unit

-- Carries an `Option Nat` for meta
scoped notation "Nat?ₘ" => Split Unit (Option Nat)

-- Carries a `Yatima.BinderInfo` for anon
scoped notation "BinderInfoₐ" => Split BinderInfo Unit

/-- Parametric representation of expressions for IPLD -/
inductive Expr (k : Kind)
  -- Variables are also used to represent recursive calls. For mutual
  -- definitions, so the second argument indicates the index of reference inside
  -- the weakly equal group. And when referencing constants, the third argument
  -- keeps track of the universe levels
  | var   : NatₐNameₘ k → Nat?ₘ k → List (UnivCid k) → Expr k
  | sort  : UnivCid k → Expr k
  | const : Nameₘ k → ConstCid k → List (UnivCid k) → Expr k
  | app   : ExprCid k → ExprCid k → Expr k
  | lam   : Nameₘ k → BinderInfoₐ k → ExprCid k → ExprCid k → Expr k
  | pi    : Nameₘ k → BinderInfoₐ k → ExprCid k → ExprCid k → Expr k
  | letE  : Nameₘ k → ExprCid k → ExprCid k → ExprCid k → Expr k
  | lit   : Split Literal Unit k → Expr k
  | proj  : Natₐ k → ExprCid k → Expr k
  deriving BEq, Inhabited

def Expr.ctorName : Expr k → String
  | .var   .. => "var"
  | .sort  .. => "sort"
  | .const .. => "const"
  | .app   .. => "app"
  | .lam   .. => "lam"
  | .pi    .. => "pi"
  | .letE  .. => "let"
  | .lit   .. => "lit"
  | .proj  .. => "proj"

end IR

namespace TC

/-- Points to a constant in an array of constants -/
abbrev ConstIdx := Nat

/-- Representation of expressions for typechecking -/
inductive Expr
  | var   : Name → Nat → Expr
  | sort  : Univ → Expr
  | const : Name → ConstIdx → List Univ → Expr
  | app   : Expr → Expr → Expr
  | lam   : Name → BinderInfo → Expr → Expr → Expr
  | pi    : Name → BinderInfo → Expr → Expr → Expr
  | letE  : Name → Expr → Expr → Expr → Expr
  | lit   : Literal → Expr
  | proj  : Nat → Expr → Expr
  deriving BEq, Inhabited

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

def type : Expr → Option Expr
  | lam  _ _ t _
  | pi   _ _ t _
  | letE _ t _ _ => some t
  | _ => none

def body : Expr → Option Expr
  | lam  _ _ _ b
  | pi   _ _ _ b
  | letE _ _ _ b => some b
  | _ => none

/-- Whether a variable is free -/
def isVarFree (name : Name) : Expr → Bool
  | var name' _ => name == name'
  | app func input => isVarFree name func || isVarFree name input
  | lam name' _ type body => isVarFree name type || (name != name' && isVarFree name body)
  | pi name' _ type body => isVarFree name type || (name != name' && isVarFree name body)
  | letE name' type value body => isVarFree name type || isVarFree name value || (name != name' && isVarFree name body)
  | proj _ body => isVarFree name body
  | _ => false

/--
Get the list of de Bruijn indices of all the variables of a `Yatima.Expr`
(helpful for debugging later)
-/
def getIndices : Expr → List Nat
  | var _ idx => [idx]
  | app func input => getIndices func ++ getIndices input
  | lam _ _ type body => getIndices type ++ getIndices body
  | pi _ _ type body => getIndices type ++ getIndices body
  | letE _ type value body => getIndices type ++ getIndices value ++ getIndices body
  | proj _ body => getIndices body
  | _ => [] -- All the rest of the cases are treated at once

/-- Get the list of bound variables in an expression -/
def getBVars : Expr → List Name
  | var name _ => [name]
  | app func input => getBVars func ++ getBVars input
  | lam _ _ type body => getBVars type ++ getBVars body
  | pi _ _ type body => getBVars type ++ getBVars body
  | letE _ type value body => getBVars type ++ getBVars value ++ getBVars body
  | proj _ body => getBVars body
  | _ => [] -- All the rest of the cases are treated at once

def ctorName : Expr → String
  | var   .. => "var"
  | sort  .. => "sort"
  | const .. => "const"
  | app   .. => "app"
  | lam   .. => "lam"
  | pi    .. => "pi"
  | letE  .. => "let"
  | lit   .. => "lit"
  | proj  .. => "proj"

-- Gets the depth of a Yatima Expr (helpful for debugging later)
def numBinders : Expr → Nat
  | lam  _ _ _ body
  | pi   _ _ _ body
  | letE _ _ _ body => 1 + numBinders body
  | _ => 0

end Expr

end TC

end Yatima
