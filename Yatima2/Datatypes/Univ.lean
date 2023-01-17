import YatimaStdLib.ByteVector
import Yatima2.Datatypes.Lean
import Yatima2.Datatypes.Lurk

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

open Lurk (F)

inductive Univ
  | zero
  | succ : F → Univ
  | max  : F → F → Univ
  | imax : F → F → Univ
  | var  : F → Univ
  deriving Inhabited, Ord, BEq

end TC

end Yatima
