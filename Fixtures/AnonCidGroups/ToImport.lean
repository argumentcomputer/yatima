import Fixtures.AnonCidGroups.ToBeImported

def Foo := MyNat -- triggering the compilation of `MyNat`
def Bar := Nat   -- triggering the compilation of `Nat`

inductive MyOtherNat
  | nada
  | mais : MyOtherNat → MyOtherNat

-- passes
inductive MyOtherNat' (α : Sort u)
  | mais : MyOtherNat' α → MyOtherNat' α

-- fails
inductive MyOtherNat'' (α : Sort u)
  | mais : α → MyOtherNat'' α
