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

def charToHex (c : Char) : String :=
  let n  := Char.toNat c;
  let d2 := n / 16;
  let d1 := n % 16;
  hexDigitRepr d2 ++ hexDigitRepr d1

/-- Generates a sequence of valid characters in Lurk from a given character. -/
def charToValidChars (c : Char) : List Char :=
  if validCharsTree.contains c then [c]
  else s!"{charToHex c}".replace "*" ":" |>.data

-- TODO: "5banonymous5d" is a hack, should be removed
def invalidNames := ["t", "nil", "_", "cons", "car", "cdr", "strcons", "eq", "quote", "5banonymous5d"]

-- TODO: This is a hack; need to talk to lurk team to add case sensitive names
def invalidCaptureNames : List Name := [
  `bEq, 
  `ofNat,
  `le, `lt,
  `trans,
  `add, `hAdd, 
  `sub, `hSub, 
  `mul, `hMul, 
  `neg,
  `div, `hDiv, 
  `mod, `hMod, 
  `pow, `hPow, 
  `append, `hAppend, 
  `orElse, `hOrElse, 
  `andThen, `hAndThen, 
  `and, `hAnd, 
  `xor, `hXor, 
  `or, `hOr, 
  `complement,
  `shiftLeft, `hShiftLeft, 
  `shiftRight, `hShiftRight,
  `getElem,
  `bind, `pure,
  `seq,
  `seqLeft, `seqRight,
  `monadLift
]

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