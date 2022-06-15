import Yatima.Typechecker.Univ
import Yatima.Expr
import Yatima.Const

namespace Yatima.Typechecker

open Std (RBMap)
abbrev Hash := Nat

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

structure Constructor (Expr : Type) where
  name   : Name
  lvls   : List Name
  type   : Expr
  ind    : ConstCid
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
  ind     : ConstCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : List (Hash × (RecursorRule Expr))
  k       : Bool
  safe    : Bool

structure Quotient (Expr : Type) where
  name : Name
  lvls : List Name
  type : Expr
  kind : QuotKind

mutual
inductive Const
  | «axiom»     : (Axiom Expr) → Const
  | «theorem»   : (Theorem Expr) → Const
  | «inductive» : (Inductive Expr) → Const
  | opaque      : (Opaque Expr) → Const
  | definition  : (Definition Expr) → Const
  | constructor : (Constructor Expr) → Const
  | recursor    : (Recursor Expr) → Const
  | quotient    : (Quotient Expr) → Const

inductive Expr
  | var   : Hash → Name → Nat → Expr
  | sort  : Hash → Univ → Expr
  | const : Hash → Name → Const → List Univ → Expr
  | app   : Hash → Expr → Expr → Expr
  | lam   : Hash → Name → BinderInfo → Expr → Expr → Expr
  | pi    : Hash → Name → BinderInfo → Expr → Expr → Expr
  | letE  : Hash → Name → Expr → Expr → Expr → Expr
  | lit   : Hash → Literal → Expr
  | lty   : Hash → LitType → Expr
  | fix   : Hash → Name → Expr → Expr
  | proj  : Hash → Nat → Expr → Expr
  deriving Inhabited
end

end Yatima.Typechecker
