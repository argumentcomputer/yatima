import Yatima.Datatypes.Expr
import Lean.Data.RBMap
import Std.Data.RBMap

def Yatima.IR.Expr.ctorName : Yatima.IR.Expr → String
  | var   .. => "var"
  | sort  .. => "sort"
  | const .. => "const"
  | app   .. => "app"
  | lam   .. => "lam"
  | pi    .. => "pi"
  | letE  .. => "letE"
  | lit   .. => "lit"
  | proj  .. => "proj"

def expr : Yatima.IR.Expr :=
  .lam (.sort Yatima.IR.Univ.zero) (.var 1 [])
def exprCtor := expr.ctorName

def map : Std.RBMap Nat Nat compare :=
  Std.RBMap.ofList [(0, 0), (1, 1), (2, 2)] _
def mapFind! := map.find! 1

def name : Lean.Name := `this.is.a.name
def nameStr := toString name
