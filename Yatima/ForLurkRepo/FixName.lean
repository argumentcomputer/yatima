import Lean

namespace Lurk 

scoped notation "Name" => Lean.Name

open Std (RBTree) in
/--
List of valid characters for Lurk identifiers. The order is shuffled to
avoid an unbalanced `RBTree`.
-/
def validCharsTree : RBTree Char compare :=
  RBTree.ofList [
    'e', 'C', '6', 'D', 'E', 'f', 'F', '7',
    'G', 'y', '8', 'z', '2', 'H', '3', '9',
    'm', 'A', 'W', 'B', '4', 'n', '5', 'X',
    'M', 'o', 's', 'p', 'i', 'N', 'j', 't',
    'k', 'S', 'Y', 'T', 'g', 'l', 'h', 'Z',
    'I', 'K', 'a', 'L', 'O', 'J', 'P', 'b',
    'U', 'u', '0', 'v', 'c', 'V', 'd', '1',
    'q', 'Q', 'w', 'R', '-', 'r', ':', 'x',
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
      if invalidNames.contains n.toLower then
        if n == "_" then "_x"
        else if n == "5banonymous5d" then "anonymous"
        else if n == "Eq" then "LEq"
        else "_" ++ n
      else n
    fixClassNameCapture (n : Name) :=
      if invalidCaptureNames.contains n then
        `_uncap ++ n
      else n
