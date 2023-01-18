import Yatima2.Datatypes.Univ
import Yatima2.Datatypes.Lurk
import YatimaStdLib.Ord

namespace Yatima

namespace IR

inductive ExprAnon
  /-- Variables are also used to represent recursive calls. When referencing
    constants, the third argument keeps track of the universe levels -/
  | var   : Nat → List Hash → ExprAnon
  | sort  : Hash → ExprAnon
  | const : Hash → List Hash → ExprAnon
  | app   : Hash → Hash → ExprAnon
  | lam   : Hash → Hash → ExprAnon
  | pi    : Hash → Hash → ExprAnon
  | letE  : Hash → Hash → Hash → ExprAnon
  | lit   : Literal → ExprAnon
  | proj  : Nat → Hash → ExprAnon
  deriving Inhabited, Ord, BEq

inductive ExprMeta
  /-- Variables are also used to represent recursive calls. For mutual
    definitions, the second argument indicates the index of reference inside
    the weakly equal group. And when referencing constants, the third argument
    keeps track of the universe levels -/
  | var   : Name → Option Nat → List Hash → ExprMeta
  | sort  : Hash → ExprMeta
  | const : Hash → List Hash → ExprMeta
  | app   : Hash → Hash → ExprMeta
  | lam   : Name → BinderInfo → Hash → Hash → ExprMeta
  | pi    : Name → BinderInfo → Hash → Hash → ExprMeta → ExprMeta
  | letE  : Name → Hash → Hash → Hash → ExprMeta
  | lit
  | proj  : Hash → ExprMeta
  deriving Inhabited, Ord, BEq

end IR

namespace TC

open Lurk (F)

inductive Expr
  /-- Variables are also used to represent recursive calls. When referencing
    constants, the third argument keeps track of the universe levels -/
  | var   : Nat → List Univ → Expr
  | sort  : Univ → Expr
  | const : F → List Univ → Expr
  | app   : Expr → Expr → Expr
  | lam   : Expr → Expr → Expr
  | pi    : Expr → Expr → Expr
  | letE  : Expr → Expr → Expr → Expr
  | lit   : Literal → Expr
  | proj  : Nat → Expr → Expr
  deriving Inhabited, Ord, BEq

end TC

end Yatima