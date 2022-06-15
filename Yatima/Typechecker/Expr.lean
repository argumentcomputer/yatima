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
  rules   : RBMap Hash (RecursorRule Expr) Ord.compare
  k       : Bool
  safe    : Bool

structure Quotient (Expr : Type) where
  name : Name
  lvls : List Name
  type : Expr
  kind : QuotKind

mutual
unsafe inductive Const
  | «axiom»     : Hash → (Axiom Expr) → Const
  | «theorem»   : Hash → (Theorem Expr) → Const
  | «inductive» : Hash → (Inductive Expr) → Const
  | opaque      : Hash → (Opaque Expr) → Const
  | definition  : Hash → (Definition Expr) → Const
  | constructor : Hash → (Constructor Expr) → Const
  | recursor    : Hash → (Recursor Expr) → Const
  | quotient    : Hash → (Quotient Expr) → Const

unsafe inductive Expr
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
end

end Yatima.Typechecker
