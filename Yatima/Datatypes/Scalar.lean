import Lurk.Hashing.Datatypes
import Yatima.Datatypes.Kind

namespace Yatima.IR

open Lurk.Hashing

structure UnivScalar (k : Kind) where
  data : ScalarPtr
  deriving BEq, Ord, Inhabited

structure ExprScalar (k : Kind) where
  data : ScalarPtr
  deriving BEq, Ord, Inhabited

structure ConstScalar (k : Kind) where
  data : ScalarPtr
  deriving BEq, Ord, Inhabited

structure AnonMeta (A : Type) (B : Type) : Type where
  anon : A
  meta : B
  deriving BEq, Ord, Inhabited

abbrev Both (A : Kind → Type) := AnonMeta (A .anon) (A .meta)

abbrev BothUnivScalar  := Both UnivScalar
abbrev BothExprScalar  := Both ExprScalar
abbrev BothConstScalar := Both ConstScalar

end Yatima.IR
