import Yatima.Cid
import Yatima.Name

namespace Yatima

inductive Univ where
  | zero
  | succ  : Univ → Univ
  | max   : Univ → Univ → Univ
  | imax  : Univ → Univ → Univ
  | param : Name → Nat → Univ
  deriving BEq, Inhabited

namespace Ipld
abbrev Name? k := Split Unit Name k
abbrev Nat?  k := Split Nat Unit k

inductive Univ (k : Kind) where
  | zero
  | succ  : UnivCid k → Univ k
  | max   : UnivCid k → UnivCid k → Univ k
  | imax  : UnivCid k → UnivCid k → Univ k
  | param : Name? k → Nat? k → Univ k
  deriving BEq, Inhabited
end Ipld

end Yatima
