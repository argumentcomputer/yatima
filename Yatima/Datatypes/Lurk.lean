namespace Lurk

abbrev F := Nat

inductive LDON
  | num : F → LDON
  | str : String → LDON
  | cons : LDON → LDON → LDON
  deriving Ord

def LDON.hash : LDON → F := fun _ => 0

end Lurk
