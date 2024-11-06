prelude
import TypeChecker.Utils.YSL.Nat
import TypeChecker.Utils.YSL.ByteArray

namespace Lurk

def N := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

abbrev F := Fin N

def F.ofNat (n : Nat) : F :=
  .ofNat n

def F.asHex (n : F) : String :=
  n.val.asHex 64

instance : Inhabited F := ⟨.ofNat 0⟩

@[match_pattern] def F.zero : F :=
  .ofNat 0

@[inline] def F.toBytes (n : F) : ByteArray :=
  let bytes := n.val.toByteArrayLE
  bytes.pushZeros $ 32 - bytes.size

@[inline] def F.ofBytes (bytes : ByteArray) : F :=
  .ofNat bytes.asLEtoNat

def F.lt (x y : F) : Bool :=
  match (decide $ x.val < N / 2, decide $ y.val < N / 2) with
    | (true, false) => false
    | (false, true) => true
    | _ => x < y

def F.le (x y : F) : Bool :=
  match (decide $ x.val < N / 2, decide $ y.val < N / 2) with
    | (true, false) => false
    | (false, true) => true
    | _ => x <= y

@[inline] def F.gt (x y : F) : Bool :=
  F.lt y x

@[inline] def F.ge (x y : F) : Bool :=
  F.le y x

end Lurk
