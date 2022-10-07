import Lurk.AST

namespace Yatima.IR

inductive PrimConst
  | nat | natZero | natSucc | string

open Std (RBMap) in
def primCidsMap : RBMap (Fin Lurk.N) PrimConst compare := .ofList [
  (sorry, .nat),
  (sorry, .natZero),
  (sorry, .natSucc),
  (sorry, .string)
]

end Yatima.IR
