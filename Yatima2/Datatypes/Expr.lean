import Yatima2.Datatypes.Univ
import YatimaStdLib.Ord

namespace Yatima

namespace IR

inductive ExprAnon
  /-- Variables are also used to represent recursive calls. When referencing
    constants, the third argument keeps track of the universe levels -/
  | var   : Hash → List Hash → ExprAnon
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
  | var   : F → List F → Expr
  | sort  : F → Expr
  | const : F → List F → Expr
  | app   : F → F → Expr
  | lam   : F → F → Expr
  | pi    : F → F → Expr
  | letE  : F → F → F → Expr
  | lit   : Literal → Expr
  | proj  : Nat → F → Expr
  deriving Inhabited, Ord, BEq

end TC

end Yatima