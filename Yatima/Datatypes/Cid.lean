-- import Ipld.Cid
import Lurk.Syntax.Expr
import Yatima.Datatypes.Kind

namespace Yatima.IR

/-- Constants to encode universe levels in IPLD -/
@[match_pattern] def UNIV : Kind → UInt64
  | .anon => 0xC0DE0001
  | .meta => 0xC0DE0002

/-- Constants to encode expressions in IPLD -/
@[match_pattern] def EXPR : Kind → UInt64
  | .anon => 0xC0DE0003
  | .meta => 0xC0DE0004

/-- Constants to encode constants in IPLD -/
@[match_pattern] def CONST : Kind → UInt64
  | .anon => 0xC0DE0005
  | .meta => 0xC0DE0006

@[match_pattern] def STORE : UInt64 := 0xC0DE0007

structure UnivCid  (k : Kind) where data : Fin Lurk.Syntax.N deriving BEq, Ord, Repr
structure ExprCid  (k : Kind) where data : Fin Lurk.Syntax.N deriving BEq, Ord, Repr
structure ConstCid (k : Kind) where data : Fin Lurk.Syntax.N deriving BEq, Ord, Repr

instance : Inhabited (UnivCid k) where 
  default := ⟨Fin.ofNat 0⟩

instance : Inhabited (ExprCid k) where 
  default := ⟨Fin.ofNat 0⟩

instance : Inhabited (ConstCid k) where 
  default := ⟨Fin.ofNat 0⟩

structure AnonMeta (A : Type) (B : Type) : Type where
  anon : A
  meta : B
  deriving BEq, Ord, Inhabited

abbrev Both (A : Kind → Type) := AnonMeta (A .anon) (A .meta)

abbrev BothUnivCid  := Both UnivCid
abbrev BothExprCid  := Both ExprCid
abbrev BothConstCid := Both ConstCid

end Yatima.IR
