import Lean.Data.HashMap

open Lean
def hmi : HashMapImp Nat String := mkHashMapImp
def hmiInsert := (hmi.insert 1 "one").1
def hmiVal := hmi.buckets
def hmiFold :=
  Id.run $ hmi.buckets.val.foldlM (init := 0) fun acc _ => acc + 1

def hashmap : Lean.HashMap String Nat := mkHashMap
def hashmapInsert := hashmap.insert "c" 3
def hashmapToList := hashmap.toList