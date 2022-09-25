import Lean.Data.RBMap
import Yatima.Datatypes.Expr

def list := [1, 2, 3, 4, 5, 6]
-- def listLength := list.length
-- def myMap (f : α → β) : List α → List β
--   | []    => []
--   | a::as => f a :: myMap f as
def listMap := list.map fun x => x + 1
def listFold := list.foldl (init := 0) fun acc x => acc + x

-- def expr : Yatima.Expr := 
--   .lam default `x default (.sort default Yatima.Univ.zero) (.var default `x 1)

-- def univ := Yatima.Univ.zero
-- def univCtor := univ.ctorName

-- def map : Std.RBMap Nat Nat compare :=
--   Std.RBMap.ofList [(0, 0), (1, 1), (2, 2)]
-- def mapInsert := map.insert 3 3

-- def strAppend := "abc" ++ "def"]
def tree : Tree Nat := .node 4 []
def treeSize := tree.size

-- inductive Vector (α : Type) : (n : Nat) → Type 
--   | nil : Vector α 0 
--   | cons : {n : Nat} → α → Vector α n → Vector α n.succ

-- set_option pp.raw true
#print List.map

-- structure thing (n : Nat) where 
--   (k : Vector α n)