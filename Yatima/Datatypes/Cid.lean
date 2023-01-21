import Ipld.Cid
import Yatima.Datatypes.Kind

namespace Yatima.IR

structure UnivCid  (k : Kind) where data : Cid deriving BEq, Ord, Inhabited, Repr
structure ExprCid  (k : Kind) where data : Cid deriving BEq, Ord, Inhabited, Repr
structure ConstCid (k : Kind) where data : Cid deriving BEq, Ord, Inhabited, Repr

structure AnonMeta (A : Type) (B : Type) : Type where
  anon : A
  meta : B
  deriving BEq, Ord, Inhabited

abbrev Both (A : Kind → Type) := AnonMeta (A .anon) (A .meta)

abbrev BothUnivCid  := Both UnivCid
abbrev BothExprCid  := Both ExprCid
abbrev BothConstCid := Both ConstCid

end Yatima.IR
