import Ipld.Cid
import Yatima.Kind

namespace Yatima
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

structure Ipld.UnivCid  (k : Kind) where data : Cid deriving BEq, Ord, Inhabited
structure Ipld.ExprCid  (k : Kind) where data : Cid deriving BEq, Ord, Inhabited
structure Ipld.ConstCid (k : Kind) where data : Cid deriving BEq, Ord, Inhabited

structure UnivCid where
  anon : Ipld.UnivCid .Anon
  meta : Ipld.UnivCid .Meta
deriving BEq, Ord, Inhabited

structure ExprCid where
  anon : Ipld.ExprCid .Anon
  meta : Ipld.ExprCid .Meta
deriving BEq, Ord, Inhabited

structure ConstCid where
  anon : Ipld.ConstCid .Anon
  meta : Ipld.ConstCid .Meta
deriving BEq, Ord, Inhabited

structure EnvCid where data : Cid deriving BEq, Ord, Inhabited

end Yatima
