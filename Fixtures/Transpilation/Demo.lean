import Lean.Data.RBMap
import Yatima

def natAdd := 100 + 200
def natSub1 := 100 - 2
def natSub2 := 100 - 200
def natMul := 32 * 32
def natLe := decide (3 <= 10)
def natBEq := 5 == 4
def natEq := decide (3 == 1000)

def list := [1, 2, 3, 4, 5, 6]
def listMap := list.map fun x => x + 1
def listFold := list.foldl (init := 0) fun acc x => acc + x
def listEq := if list = [0, 1, 2] then 0 else 1

def expr : Yatima.Expr := 
  .lam default `x default (.sort default Yatima.Univ.zero) (.var default `x 1)

def univ := @Yatima.Ipld.Univ.zero Yatima.Ipld.Kind.meta
def univIpld := Yatima.ToIpld.univToIpld univ

def map : Std.RBMap Nat Nat compare :=
  Std.RBMap.ofList [(0, 0), (1, 1), (2, 2)]
def mapInsert := map.insert 3 3

def strAppend := "abc" ++ "def"

def tree : Tree Nat := .node 4 []
def treeSize := tree.size

def name : Lean.Name := `this.is.a.name
def nameStr := toString name

#print ite