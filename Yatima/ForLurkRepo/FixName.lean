import Std.Data.RBTree

namespace Lurk 

abbrev Name := Lean.Name 

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
    'q', 'r', 'w', 'x', 'Q', 'R', '-', ':',
    '_']

/-- Generates a sequence of valid characters in Lurk from a given character. -/
def charToValidChars (c : Char) : List Char :=
  if validCharsTree.contains c then [c]
  else s!"{charToHex c}".replace "*" ":" |>.data

-- TODO: "5banonymous5d" is a hack, should be removed
def invalidNames := ["t", "nil", "_", "cons", "car", "cdr", "strcons", "eq", "quote", "5banonymous5d"]

-- TODO: This is a GIGANTIC HACK; unacceptable workaround, must be rem
def invalidCaptureNames : List Name := [`add, `hAdd]

/-- Turns a `Name` into a valid variable identifier in Lurk. -/
def fixName (name : Name) (pretty := true) : String :=
  if pretty then 
    validate $ Lean.Name.toString name false
  else 
    let name := (fixClassNameCapture name).toString.replace "." "_"
    let charsArray : Array Char := name.foldl (init := #[]) fun acc c =>
      acc.append ⟨charToValidChars c⟩
    validate ⟨charsArray.data⟩
  where 
    validate (n : String) := 
      if invalidNames.contains n then 
        if n == "_" then "_x" 
        else if n == "5banonymous5d" then "anonymous"
        else "_" ++ n
      else n
    fixClassNameCapture (n : Name) := 
      if invalidCaptureNames.contains n then 
        `_uncap ++ n
      else n
