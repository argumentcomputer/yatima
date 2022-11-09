import Lurk.Hashing.Datatypes
import Yatima.Typechecker.Datatypes
import Std.Data.RBMap.Basic

namespace Yatima.IR

open Std Lurk.Hashing Yatima.Typechecker in
def primConstsMap : RBMap ScalarPtr PrimConst compare := .ofList [
  (sorry, .nat),
  (sorry, .decT),
  (sorry, .decF),
  (sorry, .natZero),
  (sorry, .string),
  (sorry, .op .natAdd),
  (sorry, .op .natMul),
  (sorry, .op .natPow),
  (sorry, .op .natDecEq),
  (sorry, .op .natSucc)
] _

end Yatima.IR
