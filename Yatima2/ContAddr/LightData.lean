import YatimaStdLib.LightData
import Yatima2.Datatypes.Store

namespace Yatima.ContAddr

open IR

instance : Encodable UnivAnon  LightData String := sorry
instance : Encodable ExprAnon  LightData String := sorry
instance : Encodable ConstAnon LightData String := sorry
instance : Encodable UnivMeta  LightData String := sorry
instance : Encodable ExprMeta  LightData String := sorry
instance : Encodable ConstMeta LightData String := sorry

end Yatima.ContAddr
