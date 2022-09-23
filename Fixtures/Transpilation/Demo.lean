import Lean.Data.RBMap
import Yatima.Datatypes.Expr

def list := [1, 2, 3, 4, 5, 6]
def listLength := list.length

def expr : Yatima.Expr := 
  .lam default `x default (.sort default Yatima.Univ.zero) (.var default `x 1)

def univ := Yatima.Univ.zero
def univCtor := univ.ctorName

def map : Std.RBMap Nat Nat compare :=
  Std.RBMap.ofList [(0, 0), (1, 1), (2, 2)]
def mapInsert := map.insert 3 3
