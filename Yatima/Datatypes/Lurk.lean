import Lurk.Field

namespace Lurk

/-! placeholder types -/

inductive LDON
  | num : F → LDON
  | str : String → LDON
  | sym : String → LDON
  | cons : LDON → LDON → LDON
  deriving Inhabited

structure LDONHashState where
  deriving Inhabited

def LDON.commit : LDON → LDONHashState → F × LDONHashState :=
  sorry

end Lurk
