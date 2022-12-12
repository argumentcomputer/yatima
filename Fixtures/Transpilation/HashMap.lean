import Lean.Data.HashMap

def hashmap : Lean.HashMap String Nat := .ofList [("a", 1), ("b", 2)] 

def hashmapInsert := hashmap.insert "c" 3
def hashmapToList := hashmap.toList