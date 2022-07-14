prelude
import Fixtures.AnonCidGroups.ToBeImported

def Foo := MyNat -- to trigger the compilation of `MyNat`

inductive MyOtherNat
  | nada
  | more : MyOtherNat → MyOtherNat
