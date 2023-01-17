import Yatima2.Datatypes.Expr

namespace Yatima

namespace IR

structure AxiomAnon where
  lvls : Nat
  type : Hash
  safe : Bool
  deriving Ord, BEq

structure TheoremAnon where
  lvls  : Nat
  type  : Hash
  value : Hash
  deriving Ord, BEq

end IR

namespace TC

end TC

end Yatima