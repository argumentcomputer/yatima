import Lean

open Lean Compiler

def hmi : HashMapImp Nat String := mkHashMapImp
def hmiInsert := (hmi.insert 1 "one").1
-- def hmiFold := hmiInsert.a.fold (d := 0) fun acc k v => acc + k
-- set_option trace.Compiler.result true in
-- #eval compile #[``hmiFold]

def find (name : Name) : MetaM Unit := do
  let some decl ← Lean.Compiler.LCNF.getMonoDecl? name |
    IO.println s!"{name} was not found"
  IO.println "found"

#eval find ``Lean.AssocList.contains