import Yatima.Const

namespace Yatima

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

namespace Ipld
abbrev BinderInfo? k := Split BinderInfo Unit k

inductive Expr (k : Kind)
  | var   : Name? k → Nat? k → Expr k
  | sort  : UnivCid k → Expr k
  | const : Name? k → ConstCid k → List (UnivCid k) → Expr k
  | app   : ExprCid k → ExprCid k → Expr k
  | lam   : Name? k → BinderInfo? k → ExprCid k → ExprCid k → Expr k
  | pi    : Name? k → BinderInfo? k → ExprCid k → ExprCid k → Expr k
  | letE  : Name? k → ExprCid k → ExprCid k → ExprCid k → Expr k
  | lit   : Split Literal Unit k → Expr k
  | lty   : Split LitType Unit k → Expr k
  | fix   : Name? k → ExprCid k → Expr k
  | proj  : Nat? k → ExprCid k → Expr k
  deriving BEq, Inhabited
end Ipld

abbrev constHash := Ipld.ConstCid .Anon
abbrev exprHash := Ipld.ExprCid .Anon

mutual
inductive Const
  | «axiom»     : constHash → Axiom Expr → Const
  | «theorem»   : constHash → Theorem Expr → Const
  | «inductive» : constHash → Inductive Expr → Const
  | «opaque»    : constHash → Opaque Expr → Const
  | definition  : constHash → Definition Expr → Const
  | constructor : constHash → Constructor Expr → Const
  | extRecursor : constHash → ExtRecursor Expr → Const
  | intRecursor : constHash → IntRecursor Expr → Const
  | quotient    : constHash → Quotient Expr → Const

inductive Expr
  | var   : exprHash → Name → Nat → Expr
  | sort  : exprHash → Univ → Expr
  | const : exprHash → Name → Const → List Univ → Expr
  | app   : exprHash → Expr → Expr → Expr
  | lam   : exprHash → Name → BinderInfo → Expr → Expr → Expr
  | pi    : exprHash → Name → BinderInfo → Expr → Expr → Expr
  | letE  : exprHash → Name → Expr → Expr → Expr → Expr
  | lit   : exprHash → Literal → Expr
  | lty   : exprHash → LitType → Expr
  | fix   : exprHash → Name → Expr → Expr
  | proj  : exprHash → Nat → Expr → Expr
  deriving Inhabited
end

def Const.name : Const → Name
  | .axiom           _ x
  | .theorem         _ x
  | .opaque          _ x
  | .quotient        _ x
  | .definition      _ x
  | .inductive       _ x
  | .constructor     _ x
  | .intRecursor     _ x
  | .extRecursor     _ x => x.name

namespace Expr

def name : Expr → Option Name
  | lam _ name .. => some name
  | pi _ name .. => some name
  | letE _ name .. => some name
  | _ => none

def bInfo : Expr → Option BinderInfo
  | lam _ _ b _ _ => some b
  | pi _ _ b _ _ => some b
  | _ => none

def type : Expr → Option (Expr)
  | lam _ _ _ t _ => some t
  | pi _ _ _ t _ => some t
  | letE _ _ t _ _ => some t
  | _ => none

def body : Expr → Option (Expr)
  | lam _ _ _ _ b => some b
  | pi _ _ _ _ b => some b
  | letE _ _ _ _ b => some b
  | _ => none

-- Get the list of de Bruijn indices of all the variables of a Yatima `Expr` (helpful for debugging later)
def getIndices : Expr → List Nat
  | var _ _ idx => [idx]
  | app _ func input => getIndices func ++ getIndices input
  | lam _ _ _ type body => getIndices type ++ getIndices body
  | pi _ _ _ type body => getIndices type ++ getIndices body
  | letE _ _ type value body => getIndices type ++ getIndices value ++ getIndices body
  | fix _ _ body => getIndices body
  | proj _ _ body => getIndices body
  | _ => [] -- All the rest of the cases are treated at once

def getBVars : Expr → List Name
  | var _ name _ => [name]
  | app _ func input => getBVars func ++ getBVars input
  | lam _ _ _ type body => getBVars type ++ getBVars body
  | pi _ _ _ type body => getBVars type ++ getBVars body
  | letE _ _ type value body => getBVars type ++ getBVars value ++ getBVars body
  | fix _ _ body => getBVars body
  | proj _ _ body => getBVars body
  | _ => [] -- All the rest of the cases are treated at once

def ctorType : Expr → String
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

end Expr

end Yatima
