import Fixtures.AnonGroups.ToBeImported

def Foo := MyNat -- triggering the compilation of `MyNat`
def Bar := Nat   -- triggering the compilation of `Nat`

inductive MyOtherNat
  | nada
  | mais : MyOtherNat → MyOtherNat
