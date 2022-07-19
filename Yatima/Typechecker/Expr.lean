import Yatima.Typechecker.Univ
import Yatima.Const

namespace Yatima.Typechecker

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
  -- lvls   : List Name
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
  ctors   : List (Constructor Expr)
  recr    : Bool
  safe    : Bool
  refl    : Bool
  unit    : Bool

structure RecursorRule (Expr : Type) where
  ctor   : Ipld.ConstCid .Anon
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
  | «axiom»     : Ipld.ConstCid .Anon → (Axiom Expr) → Const
  | «theorem»   : Ipld.ConstCid .Anon → (Theorem Expr) → Const
  | «inductive» : Ipld.ConstCid .Anon → (Inductive Expr) → Const
  | «opaque»    : Ipld.ConstCid .Anon → (Opaque Expr) → Const
  | definition  : Ipld.ConstCid .Anon → (Definition Expr) → Const
  | constructor : Ipld.ConstCid .Anon → (Constructor Expr) → Const
  | extRecursor : Ipld.ConstCid .Anon → (ExtRecursor Expr) → Const
  | intRecursor : Ipld.ConstCid .Anon → (IntRecursor Expr) → Const
  | quotient    : Ipld.ConstCid .Anon → (Quotient Expr) → Const

inductive Expr
  | var   : Ipld.ExprCid .Anon → Name → Nat → Expr
  | sort  : Ipld.ExprCid .Anon → Univ → Expr
  | const : Ipld.ExprCid .Anon → Name → Const → List Univ → Expr
  | app   : Ipld.ExprCid .Anon → Expr → Expr → Expr
  | lam   : Ipld.ExprCid .Anon → Name → BinderInfo → Expr → Expr → Expr
  | pi    : Ipld.ExprCid .Anon → Name → BinderInfo → Expr → Expr → Expr
  | letE  : Ipld.ExprCid .Anon → Name → Expr → Expr → Expr → Expr
  | lit   : Ipld.ExprCid .Anon → Literal → Expr
  | lty   : Ipld.ExprCid .Anon → LitType → Expr
  | fix   : Ipld.ExprCid .Anon → Name → Expr → Expr
  | proj  : Ipld.ExprCid .Anon → Nat → Expr → Expr
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

def getConstHash (k : Const) : Ipld.ConstCid .Anon :=
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
