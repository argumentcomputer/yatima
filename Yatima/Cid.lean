import Yatima.Ipld.Cid

namespace Yatima
def UNIVANON  : UInt64 := 0xC0DE0001
def UNIVMETA  : UInt64 := 0xC0DE0002
def EXPRANON  : UInt64 := 0xC0DE0003
def EXPRMETA  : UInt64 := 0xC0DE0004
def CONSTANON : UInt64 := 0xC0DE0005
def CONSTMETA : UInt64 := 0xC0DE0006

def AXIOMANON        : UInt64 := 0xC0DE0007
def AXIOMMETA        : UInt64 := 0xC0DE0008
def THEOREMANON      : UInt64 := 0xC0DE0009
def THEOREMMETA      : UInt64 := 0xC0DE0010
def INDUCTIVEANON    : UInt64 := 0xC0DE0011
def INDUCTIVEMETA    : UInt64 := 0xC0DE0012
def OPAQUEANON       : UInt64 := 0xC0DE0013
def OPAQUEMETA       : UInt64 := 0xC0DE0014
def DEFINITIONANON   : UInt64 := 0xC0DE0015
def DEFINITIONMETA   : UInt64 := 0xC0DE0016
def CONSTRUCTORANON  : UInt64 := 0xC0DE0017
def CONSTRUCTORMETA  : UInt64 := 0xC0DE0018
def RECURSORRULEANON : UInt64 := 0xC0DE0019
def RECURSORRULEMETA : UInt64 := 0xC0DE0020
def RECURSORANON     : UInt64 := 0xC0DE0021
def RECURSORMETA     : UInt64 := 0xC0DE0022
def QUOTIENTANON     : UInt64 := 0xC0DE0023
def QUOTIENTMETA     : UInt64 := 0xC0DE0024
def DEFINITIONSAFETY : UInt64 := 0xC0DE0025
def QUOTKIND         : UInt64 := 0xC0DE0026

def ENV: UInt64 := 0xC0DE0027

structure UnivAnonCid  where data : Cid deriving BEq, Ord
structure UnivMetaCid  where data : Cid deriving BEq, Ord
structure ExprAnonCid  where data : Cid deriving BEq, Ord
structure ExprMetaCid  where data : Cid deriving BEq, Ord
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
