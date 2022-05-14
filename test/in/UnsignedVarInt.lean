import Yatima.Ipld.UnsignedVarInt

open UnsignedVarInt

#eval (fromVarInt (toVarInt 1)).get!.fst == 1
#eval (toVarInt 127) == { data := #[0b01111111] }
#eval (fromVarInt (toVarInt 127)).get!.fst == 127
#eval toVarInt 255
#eval (toVarInt 255 == { data := #[0b11111111, 0b00000001] })
#eval (toVarInt 255 == { data := #[0b01111111, 0b00000001] })
#eval (fromVarInt (toVarInt 255)).get!.fst == 255
#eval (toVarInt 300 == { data := #[0b10101100, 0b00000010] })
#eval (fromVarInt (toVarInt 300)).get!.fst == 300
#eval (toVarInt 16384 == { data := #[0b10000000, 0b10000000, 0b00000001] })
#eval (fromVarInt (toVarInt 16384)).get!.fst == 16384

structure Case where
  nat: Nat
  bytes: ByteArray

instance : ToString Case where
  toString case := s!"{case.nat} ↔ {case.bytes}"

/-- Test that a given test-case passes -/
def testCase (case : Case) : Bool := 
  match fromVarInt case.bytes with
  | Option.none => false
  | Option.some (n,_) =>
    toVarInt case.nat == case.bytes &&
    n == case.nat

def findFailing (cases: List Case) : List Case :=
  List.filter (fun x => not (testCase x)) cases

def cases : List Case := 
  [ Case.mk 1   { data := #[0b00000001] }
  , Case.mk 127 { data := #[0b01111111] }
  , Case.mk 128 { data := #[0b10000000, 0b00000001] }
  , Case.mk 255 { data := #[0b11111111, 0b00000001] }
  , Case.mk 300 { data := #[0b10101100, 0b00000010] }
  , Case.mk 16384 { data := #[0b10000000, 0b10000000, 0b000000001] }
  ]

#eval findFailing cases
