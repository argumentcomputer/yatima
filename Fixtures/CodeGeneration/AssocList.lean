import Lean

def assoc : Lean.AssocList Nat String := [(1, "one"), (2, "two")].toAssocList'
def assocInsert := assoc.insert 3 "three"
def assocContains := assocInsert.contains 2
def assocToList := assocInsert.toList