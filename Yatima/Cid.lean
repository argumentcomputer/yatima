import Ipld.Cid
import Yatima.Kind

namespace Yatima

namespace Ipld
def UNIV : (k : Kind) → UInt64
  | .Anon => 0xC0DE0001
  | .Meta => 0xC0DE0002
def EXPR : (k : Kind) → UInt64
  | .Anon => 0xC0DE0003
  | .Meta => 0xC0DE0004
def CONST : (k : Kind) → UInt64
  | .Anon => 0xC0DE0005
  | .Meta => 0xC0DE0006

def ENV: UInt64 := 0xC0DE0007

structure UnivCid  (k : Kind) where data : Cid deriving BEq, Ord, Inhabited
structure ExprCid  (k : Kind) where data : Cid deriving BEq, Ord, Inhabited
structure ConstCid (k : Kind) where data : Cid deriving BEq, Ord, Inhabited

structure Both (A : Kind → Type) : Type where
  anon : A .Anon
  meta : A .Meta

instance (A : Kind → Type) [(k : Kind) → BEq (A k)] : BEq (Both A) :=
  { beq := fun a b => BEq.beq a.anon b.anon && BEq.beq a.meta b.meta }

end Ipld

abbrev UnivCid := Ipld.Both Ipld.UnivCid
abbrev ExprCid := Ipld.Both Ipld.ExprCid
abbrev ConstCid := Ipld.Both Ipld.ConstCid

structure EnvCid where data : Cid deriving BEq, Ord, Inhabited

end Yatima
