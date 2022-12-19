import Lean.Data.RBMap


-- #print List.hasDecidableLt
def charLt := decide $ 'a' < 'b'

def charListLt := decide $ ['a', 'b'] < ['b', 'c']

def listDecLt := decide $ [1, 2, 3] < [2, 3, 4]

def stringDecLt := decide $ "123" < "234"
def rbmap : Lean.RBMap String Nat compare := Lean.RBMap.ofList [("a", 1), ("b", 2)]

def rbmapInsert := rbmap.insert "c" 3
def rbmapToList := rbmapInsert.toList
