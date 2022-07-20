import Yatima.Typechecker.Univ
import Yatima.Const

namespace Yatima.Typechecker

abbrev hashConst := Ipld.ConstCid .Anon
abbrev hashExpr  := Ipld.ExprCid .Anon

structure Axiom (Expr : Type) where
  name : Name
  lvls : List Name
  type : Expr
  safe : Bool

structure Theorem (Expr : Type) where
  name  : Name
  lvls  : List Name
  type  : Expr
  value : Expr

structure Opaque (Expr : Type) where
  name  : Name
  lvls  : List Name
  type  : Expr
  value : Expr
  safe  : Bool

structure Definition (Expr : Type) where
  name   : Name
  lvls   : List Name
  type   : Expr
  value  : Expr
  safety : DefinitionSafety

structure Constructor (Expr : Type) where
  name   : Name
  lvls   : List Name
  type   : Expr
  -- idx    : Nat
  params : Nat
  fields : Nat
  rhs    : Expr
  -- safe   : Bool

structure Inductive (Expr : Type) where
  name    : Name
  lvls    : List Name
  type    : Expr
  params  : Nat
  indices : Nat
  recr    : Bool
  safe    : Bool
  refl    : Bool
  unit    : Bool
  struct  : Option (Constructor Expr)

structure RecursorRule (Expr : Type) where
  ctor   : hashConst
  fields : Nat
  rhs    : Expr

structure ExtRecursor (Expr : Type) where
  name    : Name
  lvls    : List Name
  type    : Expr
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : List (RecursorRule Expr)
  k       : Bool

structure IntRecursor (Expr : Type) where
  name    : Name
  lvls    : List Name
  type    : Expr
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  k       : Bool

structure Quotient (Expr : Type) where
  name : Name
  lvls : List Name
  type : Expr
  kind : QuotKind

mutual
inductive Const
  | «axiom»     : hashConst → (Axiom Expr) → Const
  | «theorem»   : hashConst → (Theorem Expr) → Const
  | «inductive» : hashConst → (Inductive Expr) → Const
  | «opaque»    : hashConst → (Opaque Expr) → Const
  | definition  : hashConst → (Definition Expr) → Const
  | constructor : hashConst → (Constructor Expr) → Const
  | extRecursor : hashConst → (ExtRecursor Expr) → Const
  | intRecursor : hashConst → (IntRecursor Expr) → Const
  | quotient    : hashConst → (Quotient Expr) → Const

inductive Expr
  | var   : hashExpr → Name → Nat → Expr
  | sort  : hashExpr → Univ → Expr
  | const : hashExpr → Name → Const → List Univ → Expr
  | app   : hashExpr → Expr → Expr → Expr
  | lam   : hashExpr → Name → BinderInfo → Expr → Expr → Expr
  | pi    : hashExpr → Name → BinderInfo → Expr → Expr → Expr
  | letE  : hashExpr → Name → Expr → Expr → Expr → Expr
  | lit   : hashExpr → Literal → Expr
  | lty   : hashExpr → LitType → Expr
  | fix   : hashExpr → Name → Expr → Expr
  | proj  : hashExpr → Nat → Expr → Expr
  deriving Inhabited
end

def getConstType (k : Const) : Expr :=
  match k with
  | .axiom _ x => x.type
  | .theorem _ x => x.type
  | .inductive _ x => x.type
  | .opaque _ x => x.type
  | .definition _ x => x.type
  | .constructor _ x => x.type
  | .intRecursor _ x => x.type
  | .extRecursor _ x => x.type
  | .quotient _ x => x.type

def getConstHash (k : Const) : hashConst :=
  match k with
  | .axiom h _ => h
  | .theorem h _ => h
  | .inductive h _ => h
  | .opaque h _ => h
  | .definition h _ => h
  | .constructor h _ => h
  | .intRecursor h _ => h
  | .extRecursor h _ => h
  | .quotient h _ => h

end Yatima.Typechecker
