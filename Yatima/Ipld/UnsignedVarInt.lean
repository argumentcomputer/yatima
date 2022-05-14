import Yatima.Ipld.Utils

namespace UnsignedVarInt

def toVarIntCore : Nat → Nat → List UInt8
| 0, n => []
| fuel + 1, n =>
  let b: UInt8 := UInt8.ofNat (n % 128)
  let n' := n / 128
  if n' = 0 then [b]
  else (b + 128) :: (toVarIntCore fuel n')

def toVarInt (n: Nat) : ByteArray := 
  (toVarIntCore (n+1) n).toByteArray

def fromVarIntCore : Nat → Nat → List UInt8 → Nat → Option (Nat × List UInt8)
| 0, i, bs, n => some (n, bs)
| fuel + 1, i, [], n => none
| fuel + 1, i, b :: bs, n => 
  let b' := Nat.shiftLeft (UInt8.toNat b % 128) (i * 7)
  if b / 128 == 0 then (n + b', bs) else fromVarIntCore fuel (i + 1) bs (n + b')

def fromVarInt (b: ByteArray) : Option (Nat × ByteArray) :=
  --Option.bind (fromVarIntCore b.length 0 b 0) $ fun ()
  match fromVarIntCore b.size 0 b.toList 0 with
  | some (num, list) => some (num, list.toByteArray)
  | none => none

instance : BEq ByteArray where
  beq a b := a.data == b.data

end UnsignedVarInt
