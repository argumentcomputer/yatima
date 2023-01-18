import YatimaStdLib.ByteVector
import Yatima2.Datatypes.Lean

namespace Yatima

namespace IR

abbrev Hash := ByteVector 32

inductive UnivAnon
  | zero
  | succ : Hash → UnivAnon
  | max  : Hash → Hash → UnivAnon
  | imax : Hash → Hash → UnivAnon
  | var  : Nat → UnivAnon
  deriving Inhabited, Ord, BEq

inductive UnivMeta
  | zero
  | succ : Hash → UnivMeta
  | max  : Hash → Hash → UnivMeta
  | imax : Hash → Hash → UnivMeta
  | var  : Name → UnivMeta
  deriving Inhabited, Ord, BEq

end IR

namespace TC

inductive Univ
  | zero
  | succ : Univ → Univ
  | max  : Univ → Univ → Univ
  | imax : Univ → Univ → Univ
  | var  : Nat → Univ
  deriving Inhabited, Ord, BEq

end TC

end Yatima
