import Yatima.Datatypes.Expr
import Lean.Data.RBMap

def expr : Yatima.TC.Expr :=
  .lam `x default (.sort Yatima.TC.Univ.zero) (.var `x 1)
def exprCtor := expr.ctorName

def univ := @Yatima.IR.Univ.zero Yatima.IR.Kind.meta
def univCtor := univ.ctorName

-- def map : Std.RBMap Nat Nat compare :=
--   Std.RBMap.ofList [(0, 0), (1, 1), (2, 2)] _
-- def mapInsert := map.insert 3 3

def tree : Tree Nat := .node 4 [.node 2 []]
def treeSize := tree.size

def name : Lean.Name := `this.is.a.name
def nameStr := toString name
