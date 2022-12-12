def natAdd := 100 + 200
def natSub1 := 100 - 2
def natSub2 := 100 - 200
def natMul := 32 * 32
def natDiv1 := 2 / 3
def natDiv2 := 100 / 3
def natMod1 := 37 % 2
def natMod2 := 37 % 0
def natLe := decide (3 <= 10)
def natBEqF := 5 == 4
def natBEqT := 5 == 5
def natEqF := decide (3 == 1000)
def natEqT := decide (3 == 3)
def natMatch : Nat → Nat
  | 0 => 0
  | _ + 1 => 10
def natMatchApp := natMatch 2
def natMatchRec : Nat → Nat
  | 0 => 0
  | n + 1 => natMatchRec n + 2 
def natMatchRecApp := natMatchRec 10
def natRepr := Nat.repr 0x16a8


def fin10 : (Fin 10) := 5
def finAdd1 : (Fin 10) := 1 + 1
def finAdd2 : (Fin 10) := 7 + 8

def uint32If (n : UInt32) : UInt32 := 
  if n ≥ 2 then 10 else 20

def uint32If0 : UInt32 := uint32If 0
def uint32If3 : UInt32 := uint32If 3

def charA := 'a'
def charOfNat := Char.ofNat 97 
def charToNat := Char.toNat 'a'
def charUTF8Size := Char.utf8Size 'a'
def charToUpper := charA.toUpper
def charLetterLike := Lean.isLetterLike charA
def charIsEsc := Lean.isIdBeginEscape charA
def charIsIdFirstA := Lean.isIdFirst 'a'
def charIsIdFirst? := Lean.isIdFirst '?'
def charIsIdRest := Lean.isIdRest '?'

def list : List Nat := [1, 2, 3, 4, 5, 6]
def listMap := list.map fun x => x + 1
def listFoldl := list.foldl (init := 0) fun acc x => acc + x
def listBeq := list == [1, 2, 3, 4, 5, 6]
def listEqF := decide (list = [0, 1, 2])
def listEqT := decide (list = [1, 2, 3, 4, 5, 6])

def abcd := "abcd"
def efg := "efg"
def stringAppendInst := abcd ++ efg 
def stringAppend := String.append abcd efg 
def stringLength := abcd.length
def stringAppendLength := stringAppend.length
def stringBEqF := abcd == efg
def stringBEqT := abcd == abcd
def stringEqF := decide (abcd = efg)
def stringEqT := decide (abcd = abcd)
def stringGet1 := abcd.get ⟨0⟩
def stringGet2 := abcd.get ⟨4⟩
def stringGet? := abcd.get? ⟨1⟩
def stringEscapePart := Lean.Name.escapePart abcd
def stringMaybeEsc := Lean.Name.toStringWithSep.maybeEscape true abcd
def stringGet := abcd.get 0
def stringNext := abcd.next 0
def stringExtract := abcd.extract 0 ⟨4⟩
def stringToSubstring := "hello".toSubstring
def stringAny := "hello".any Char.isAlpha

open Lean 
def isIdLike (s : String) : Bool :=
  s.length > 0 && 
  isIdFirst (s.get 0) && 
  (s.toSubstring.drop 1).all isIdRest

def stringIsIdLike := isIdLike "_ident?"

def substringAny := "".toSubstring.any Char.isAlpha
def substringAll := "hello".toSubstring.all Char.isAlpha

def name : Lean.Name := `hello
def nameMkStr1 := Lean.Name.mkStr1 "hello"
def nameAppend : Lean.Name := `hello ++ `world
def nameWithSep := (`hello).toStringWithSep "." true
def nameToString := nameAppend.toString
def nameHash := (`hi).hash
def nameCap := (`hi).capitalize

def optNat := some 14
def optMap := optNat.map fun n => n + 1
def optNone : Option Nat := none

mutual

def f : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * g n

def g : Nat → Nat
  | 0 => 1
  | n + 1 => f n

end

def f10 := f 10