import LightData
import Yatima.Datatypes.Store

namespace Yatima.ContAddr

open IR

instance : Encodable UnivAnon  LightData String := sorry
instance : Encodable ExprAnon  LightData String := sorry
instance : Encodable ConstAnon LightData String := sorry
instance : Encodable UnivMeta  LightData String := sorry
instance : Encodable ExprMeta  LightData String := sorry
instance : Encodable ConstMeta LightData String := sorry

def hashUnivAnon (x : UnivAnon) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

def hashExprAnon (x : ExprAnon) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

def hashConstAnon (x : ConstAnon) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

def hashUnivMeta (x : UnivMeta) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

def hashExprMeta (x : ExprMeta) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

def hashConstMeta (x : ConstMeta) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

end Yatima.ContAddr
