import Ipld.Cid
import Yatima.Datatypes.Kind

namespace Yatima.IR

/-- Constants to encode universe levels in IPLD -/
@[matchPattern] def UNIV : Kind → UInt64
  | .anon => 0xC0DE0001
  | .meta => 0xC0DE0002

/-- Constants to encode expressions in IPLD -/
@[matchPattern] def EXPR : Kind → UInt64
  | .anon => 0xC0DE0003
  | .meta => 0xC0DE0004

/-- Constants to encode constants in IPLD -/
@[matchPattern] def CONST : Kind → UInt64
  | .anon => 0xC0DE0005
  | .meta => 0xC0DE0006

@[matchPattern] def STORE : UInt64 := 0xC0DE0007

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
