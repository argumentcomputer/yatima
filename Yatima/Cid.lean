import Ipld.Cid
import Yatima.Kind

namespace Yatima
def UNIVANON  : UInt64 := 0xC0DE0001
def UNIVMETA  : UInt64 := 0xC0DE0002
def EXPRANON  : UInt64 := 0xC0DE0003
def EXPRMETA  : UInt64 := 0xC0DE0004
def CONSTANON : UInt64 := 0xC0DE0005
def CONSTMETA : UInt64 := 0xC0DE0006

def ENV: UInt64 := 0xC0DE0007

structure UnivAnonCid  where data : Cid deriving BEq, Ord
structure UnivMetaCid  where data : Cid deriving BEq, Ord
structure ExprAnonCid  where data : Cid deriving BEq, Ord
structure ExprMetaCid  where data : Cid deriving BEq, Ord
structure ConstAnonCid where data : Cid deriving BEq, Ord
structure ConstMetaCid where data : Cid deriving BEq, Ord

structure UnivPureCid where
  anon : UnivAnonCid
  meta : UnivMetaCid
deriving BEq, Ord

structure ExprPureCid where
  anon : ExprAnonCid
  meta : ExprMetaCid
deriving BEq, Ord

structure ConstPureCid where
  anon : ConstAnonCid
  meta : ConstMetaCid
deriving BEq, Ord

@[reducible] def UnivCid : Kind → Type
| .Pure => UnivPureCid
| .Anon => UnivAnonCid
| .Meta => UnivMetaCid
instance : BEq (UnivCid k) where
  beq := kindEtaExpand k with BEq.beq
instance : Ord (UnivCid k) where
  compare := kindEtaExpand k with Ord.compare

@[reducible] def ExprCid : Kind → Type
| .Pure => ExprPureCid
| .Anon => ExprAnonCid
| .Meta => ExprMetaCid
instance : BEq (ExprCid k) where
  beq := kindEtaExpand k with BEq.beq
instance : Ord (ExprCid k) where
  compare := kindEtaExpand k with Ord.compare

@[reducible] def ConstCid : Kind → Type
| .Pure => ConstPureCid
| .Anon => ConstAnonCid
| .Meta => ConstMetaCid
instance : BEq (ConstCid k) where
  beq := kindEtaExpand k with BEq.beq
instance : Ord (ConstCid k) where
  compare := kindEtaExpand k with Ord.compare

structure EnvCid where data : Cid deriving BEq

end Yatima
