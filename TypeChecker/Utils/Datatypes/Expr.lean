prelude
import TypeChecker.Utils.Datatypes.Univ
import TypeChecker.Utils.YSL.Field
import TypeChecker.Utils.YSL.Ord
import TypeChecker.Utils.YSL.List

namespace Yatima.IR

instance (priority := high) : Hashable Literal where hash
  | .natVal x => hash (0, x)
  | .strVal x => hash (1, x)

inductive Expr
  /-- Variables are also used to represent recursive calls. When referencing
    constants, the second argument keeps track of the universe levels -/
  | var   : Nat → List Univ → Expr
  | sort  : Univ → Expr
  | const : Lurk.F → List Univ → Expr
  | app   : Expr → Expr → Expr
  | lam   : Expr → Expr → Expr
  | pi    : Expr → Expr → Expr
  | letE  : Expr → Expr → Expr → Expr
  | lit   : Literal → Expr
  | proj  : Nat → Expr → Expr
  deriving Inhabited, Ord, BEq, Hashable, Repr

end Yatima.IR
