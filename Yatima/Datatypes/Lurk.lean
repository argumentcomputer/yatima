namespace Lurk

/-! placeholder types -/

structure F where
  val : Nat
  deriving Inhabited, Ord, BEq

instance : ToString F := ⟨toString ∘ F.val⟩

inductive LDON
  | u64 : UInt64 → LDON
  | num : F → LDON
  | str : String → LDON
  | sym : String → LDON
  | cons : LDON → LDON → LDON
  deriving Inhabited

structure LDONHashState where
  deriving Inhabited

def LDON.commit : LDON → LDONHashState → F × LDONHashState :=
  default

end Lurk
