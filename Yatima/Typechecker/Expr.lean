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

structure Inductive (Expr : Type) where
  name    : Name
  lvls    : List Name
  type    : Expr
  params  : Nat
  indices : Nat
  ctors   : List (Name × Expr)
  recr    : Bool
  safe    : Bool
  refl    : Bool
  nest    : Bool
  unit    : Bool

structure Constructor (Expr : Type) where
  name   : Name
  lvls   : List Name
  type   : Expr
  -- TODO: this might not be necessary at all
  -- ind    : ConstCid
  idx    : Nat
  params : Nat
  fields : Nat
  safe   : Bool

structure RecursorRule (Expr : Type) where
  fields : Nat
  rhs    : Expr

structure Recursor (Expr : Type) where
  name    : Name
  lvls    : List Name
  type    : Expr
  -- TODO: this might not be necessary at all
  -- ind     : ConstCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : List (ConstAnonCid × (RecursorRule Expr))
  k       : Bool
  safe    : Bool

structure Quotient (Expr : Type) where
  name : Name
  lvls : List Name
  type : Expr
  kind : QuotKind

mutual
inductive Const
  | «axiom»     : ConstAnonCid → (Axiom Expr) → Const
  | «theorem»   : ConstAnonCid → (Theorem Expr) → Const
  | «inductive» : ConstAnonCid → (Inductive Expr) → Const
  | opaque      : ConstAnonCid → (Opaque Expr) → Const
  | definition  : ConstAnonCid → (Definition Expr) → Const
  | constructor : ConstAnonCid → (Constructor Expr) → Const
  | recursor    : ConstAnonCid → (Recursor Expr) → Const
  | quotient    : ConstAnonCid → (Quotient Expr) → Const

inductive Expr
  | var   : ExprAnonCid → Name → Nat → Expr
  | sort  : ExprAnonCid → Univ → Expr
  | const : ExprAnonCid → Name → Const → List Univ → Expr
  | app   : ExprAnonCid → Expr → Expr → Expr
  | lam   : ExprAnonCid → Name → BinderInfo → Expr → Expr → Expr
  | pi    : ExprAnonCid → Name → BinderInfo → Expr → Expr → Expr
  | letE  : ExprAnonCid → Name → Expr → Expr → Expr → Expr
  | lit   : ExprAnonCid → Literal → Expr
  | lty   : ExprAnonCid → LitType → Expr
  | fix   : ExprAnonCid → Name → Expr → Expr
  | proj  : ExprAnonCid → Nat → Expr → Expr
  deriving Inhabited
end

def getConstType (k : Const) : Expr :=
  match k with
  | .«axiom» _ x => x.type
  | .«theorem» _ x => x.type
  | .«inductive» _ x => x.type
  | .opaque _ x => x.type
  | .definition _ x => x.type
  | .constructor _ x => x.type
  | .recursor _ x => x.type
  | .quotient _ x => x.type

def getConstHash (k : Const) : ConstAnonCid :=
  match k with
  | .«axiom» h _ => h
  | .«theorem» h _ => h
  | .«inductive» h _ => h
  | .opaque h _ => h
  | .definition h _ => h
  | .constructor h _ => h
  | .recursor h _ => h
  | .quotient h _ => h

end Yatima.Typechecker
