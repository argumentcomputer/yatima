import Lean.Data.RBMap
import Yatima

def expr : Yatima.TC.Expr := 
  .lam default `x default (.sort default Yatima.TC.Univ.zero) (.var default `x 1)

def univ := @Yatima.IR.Univ.zero Yatima.IR.Kind.meta
def univCtor := univ.ctorName

def map : Std.RBMap Nat Nat compare :=
  Std.RBMap.ofList [(0, 0), (1, 1), (2, 2)]
def mapInsert := map.insert 3 3

def strAppend := "abc" ++ "def"

def tree : Tree Nat := .node 4 []
def treeSize := tree.size

def name : Lean.Name := `this.is.a.name
def nameStr := toString name
