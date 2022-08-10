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

/-- Turns a `Name` into a valid variable identifier in Lurk. -/
def fixName (name : Name) (pretty := true) : String :=
  if pretty then 
    validate $ Lean.Name.toString name false
  else 
    let name := name.toString.replace "." "_" -- |>.replace "_" "??" FIX: If they haven't merged the change yet, we need to revist this.
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
