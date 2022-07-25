import Std.Data.RBTree

namespace Yatima.Transpiler

open Std (RBTree)

/--
List of valid characters for Lurk identifiers. The order is shuffled to
avoid an unbalanced `RBTree`.
-/
def validCharsTree : RBTree Char compare :=
  RBTree.ofList [
    'e', 'f', '6', '7', 'C', 'D', 'E', 'F',
    'G', 'H', '8', '9', 'y', 'z', '2', '3',
    'm', 'n', 'W', 'X', 'A', 'B', '4', '5',
    'M', 'N', 's', 't', 'o', 'p', 'i', 'j',
    'k', 'l', 'Y', 'Z', 'S', 'T', 'g', 'h',
    'I', 'J', 'a', 'b', 'K', 'L', 'O', 'P',
    'U', 'V', '0', '1', 'u', 'v', 'c', 'd',
    'q', 'r', 'w', 'x', 'Q', 'R', '-', ':']

/-- Generates a sequence of valid characters in Lurk from a given character. -/
def charToValidChars (c : Char) : List Char :=
  if validCharsTree.contains c then [c]
  else s!"::{charToHex c}::".replace "*" "-" |>.data

/-- Turns a `String` into a valid variable identifier in Lurk. -/
def fixName (name : String) : String :=
  let name := name.replace "." ":" |>.replace "_" "-"
  let charsArray : Array Char := name.foldl (init := #[]) fun acc c =>
    acc.append ⟨charToValidChars c⟩
  ⟨charsArray.data⟩

end Yatima.Transpiler
