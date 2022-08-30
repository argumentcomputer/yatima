import Ipld.Cid
import Yatima.Datatypes.Kind

namespace Yatima

namespace Ipld

/-- Constants to encode universe levels in IPLD -/
def UNIV : Kind → UInt64
  | .anon => 0xC0DE0001
  | .meta => 0xC0DE0002

/-- Constants to encode expressions in IPLD -/
def EXPR : Kind → UInt64
  | .anon => 0xC0DE0003
  | .meta => 0xC0DE0004

/-- Constants to encode constants in IPLD -/
def CONST : Kind → UInt64
  | .anon => 0xC0DE0005
  | .meta => 0xC0DE0006

def STORE : UInt64 := 0xC0DE0007

structure UnivCid  (k : Kind) where data : Cid deriving BEq, Ord, Inhabited, Repr
structure ExprCid  (k : Kind) where data : Cid deriving BEq, Ord, Inhabited, Repr
structure ConstCid (k : Kind) where data : Cid deriving BEq, Ord, Inhabited, Repr

structure AnonMeta (A : Type) (B : Type) : Type where
  anon : A
  meta : B
  deriving BEq, Ord, Inhabited

abbrev Both (A : Kind → Type) := AnonMeta (A .anon) (A .meta)

end Ipld

abbrev UnivCid  := Ipld.Both Ipld.UnivCid
abbrev ExprCid  := Ipld.Both Ipld.ExprCid
abbrev ConstCid := Ipld.Both Ipld.ConstCid

structure StoreCid where data : Cid deriving BEq, Ord, Inhabited

end Yatima
