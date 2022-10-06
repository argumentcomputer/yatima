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

/--
  The type info is a simplified form of the value's type, with only relevant
  information for conversion checking, in order to get proof irrelevance and equality
  of unit-like values. Expressions starts with default values in all nodes until they
  are correctly populated by the typechecker.

  - `struct? idx` gives the structure index of the expression's type
     in case it is a structure
  - `unit?` tells us if the expression's type is unit-like
  - `proof?` tells us if the expression's type is a proposition (belong to `Prop`)
  - `prop?` tells us if the expression's type is `Prop` itself
-/
structure TypeInfo where
  struct? : Option Nat
  unit?   : Bool
  proof?  : Bool
  prop?   : Bool
  deriving Inhabited

instance : BEq TypeInfo where beq _ _ := true

/-- Representation of expressions for typechecking and transpilation -/
inductive Expr
  | var   : TypeInfo → Name → Nat → Expr
  | sort  : TypeInfo → Univ → Expr
  | const : TypeInfo → Name → ConstIdx → List Univ → Expr
  | app   : TypeInfo → Expr → Expr → Expr
  | lam   : TypeInfo → Name → BinderInfo → Expr → Expr → Expr
  | pi    : TypeInfo → Name → BinderInfo → Expr → Expr → Expr
  | letE  : TypeInfo → Name → Expr → Expr → Expr → Expr
  | lit   : TypeInfo → Literal → Expr
  | proj  : TypeInfo → Nat → Expr → Expr
  deriving BEq, Inhabited

namespace Expr

def info : Expr → TypeInfo
  | var   info ..
  | sort  info ..
  | const info ..
  | app   info ..
  | lam   info ..
  | pi    info ..
  | letE  info ..
  | lit   info ..
  | proj  info .. => info

def name : Expr → Option Name
  | var   _ n _
  | const _ n ..
  | lam   _ n ..
  | pi    _ n ..
  | letE  _ n .. => some n
  | _ => none

def bInfo : Expr → Option BinderInfo
  | lam _ _ b ..
  | pi  _ _ b .. => some b
  | _ => none

def type : Expr → Option Expr
  | lam  _ _ _ ty _
  | pi   _ _ _ ty _
  | letE _ _ ty _ _ => some ty
  | _ => none

def body : Expr → Option Expr
  | lam  _ _ _ _ b
  | pi   _ _ _ _ b
  | letE _ _ _ _ b => some b
  | _ => none

/-- Whether a variable is free -/
def isVarFree (name : Name) : Expr → Bool
  | var _ name' _ => name == name'
  | app _ func input => isVarFree name func || isVarFree name input
  | lam _ name' _ type body => isVarFree name type || (name != name' && isVarFree name body)
  | pi _ name' _ type body => isVarFree name type || (name != name' && isVarFree name body)
  | letE _ name' type value body => isVarFree name type || isVarFree name value || (name != name' && isVarFree name body)
  | proj _ _ body => isVarFree name body
  | _ => false

/--
Get the list of de Bruijn indices of all the variables of a `Yatima.Expr`
(helpful for debugging later)
-/
def getIndices : Expr → List Nat
  | var _ _ idx => [idx]
  | app _ func input => getIndices func ++ getIndices input
  | lam _ _ _ type body => getIndices type ++ getIndices body
  | pi _ _ _ type body => getIndices type ++ getIndices body
  | letE _ _ type value body => getIndices type ++ getIndices value ++ getIndices body
  | proj _ _ body => getIndices body
  | _ => [] -- All the rest of the cases are treated at once

/-- Get the list of bound variables in an expression -/
def getBVars : Expr → List Name
  | var _ name _ => [name]
  | app _ func input => getBVars func ++ getBVars input
  | lam _ _ _ type body => getBVars type ++ getBVars body
  | pi _ _ _ type body => getBVars type ++ getBVars body
  | letE _ _ type value body => getBVars type ++ getBVars value ++ getBVars body
  | proj _ _ body => getBVars body
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
  | lam  _ _ _ _ body
  | pi   _ _ _ _ body
  | letE _ _ _ _ body => 1 + numBinders body
  | _ => 0

/--
Remove all binders from an expression, converting a lambda into
an "implicit lambda". This is useful for constructing the `rhs` of
recursor rules.
-/
def toImplicitLambda : Expr → Expr
  | .lam _ _ _ _ body => toImplicitLambda body
  | x => x

end Expr

end TC

end Yatima
