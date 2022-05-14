import Yatima.Ipld.Cid

namespace Yatima
def UNIVANON: UInt64 := 0xC0DE0001
def UNIVMETA: UInt64 := 0xC0DE0002
def EXPRANON: UInt64 := 0xC0DE0003
def EXPRMETA: UInt64 := 0xC0DE0004
def CONSTANON: UInt64 := 0xC0DE0005
def CONSTMETA: UInt64 := 0xC0DE0006

def ENV: UInt64 := 0xC0DE0007

structure UnivAnonCid where data : Cid deriving BEq, Ord
structure UnivMetaCid where data : Cid deriving BEq, Ord
structure ExprAnonCid where data : Cid deriving BEq, Ord
structure ExprMetaCid where data : Cid deriving BEq, Ord
structure ConstAnonCid where data : Cid deriving BEq, Ord
structure ConstMetaCid where data : Cid deriving BEq, Ord

structure UnivCid where 
  anon : UnivAnonCid
  meta : UnivMetaCid
deriving BEq, Ord

structure ExprCid where 
  anon : ExprAnonCid
  meta : ExprMetaCid
deriving BEq, Ord

structure ConstCid where
  anon : ConstAnonCid
  meta : ConstMetaCid
deriving BEq, Ord

structure EnvCid where data : Cid deriving BEq

end Yatima
