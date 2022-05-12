import Yatima.Ipld.DagCbor
import Std.Data.RBTree

open Std (RBNode RBMap)

#eval (EStateM.run next { bytes := ByteArray.mk #[0,1,2], pos := 0 })
#eval (EStateM.run (take 3) { bytes := ByteArray.mk #[0,1,2], pos := 0 })
#eval (EStateM.run (tag 0) { bytes := ByteArray.mk #[0,1,2], pos := 0 })

#eval serialize (Ipld.bytes (ByteArray.mk #[1, 2, 3]))
#eval deserialize (ByteArray.mk #[67, 1, 2, 3])

instance : BEq (Except DeserializeError Ipld) where
  beq
  | Except.ok x, Except.ok y => x == y
  | Except.error x, Except.error y => x == y
  | _, _ => false

def ser_de (x: Ipld) : Bool :=
  deserialize (serialize x) == Except.ok x

def ser_is (x: Ipld) (y: Array UInt8) : Bool :=
  (serialize x) == ByteArray.mk y

#eval ser_de Ipld.null
#eval ser_is Ipld.null #[246]
#eval ser_de (Ipld.bool true)
#eval ser_is (Ipld.bool true) #[245]
#eval ser_de (Ipld.bool false)
#eval ser_is (Ipld.bool false) #[244]
#eval ser_de (Ipld.number 0)
#eval ser_is (Ipld.number 0) #[0]
#eval ser_de (Ipld.number 0x17)
#eval ser_is (Ipld.number 0x17) #[23]
#eval ser_de (Ipld.number 0x18)
#eval ser_is (Ipld.number 0x18) #[24,24]
#eval ser_de (Ipld.number 0xff)
#eval ser_is (Ipld.number 0xff) #[24,255]
#eval ser_de (Ipld.number 256)
#eval ser_is (Ipld.number 0x100) #[25,1,0]
#eval ser_de (Ipld.number 0xffff)
#eval ser_is (Ipld.number 0xffff) #[25,255,255]
#eval ser_de (Ipld.number 0x10000)
#eval ser_is (Ipld.number 0x10000) #[26,0,1,0,0]
#eval ser_de (Ipld.number 0xffffffff)
#eval ser_is (Ipld.number 0xffffffff) #[26,255,255,255,255]
#eval ser_de (Ipld.number 0x100000000)
#eval ser_is (Ipld.number 0x100000000) #[27, 0,0,0,1,0,0,0,0]

#eval ser_de (Ipld.string "foobar")
#eval ser_de (Ipld.bytes (ByteArray.mk #[0, 8, 4, 0]))
#eval ser_de (Ipld.bytes  (ByteArray.mk #[0, 8, 4, 0]))

#eval ser_de (Ipld.string "Hello")
#eval ser_is (Ipld.string "Hello") #[0x65, 0x48, 0x65, 0x6c, 0x6c, 0x6f]
#eval ser_de (Ipld.bytes "Hello".toUTF8)
#eval ser_is (Ipld.bytes "Hello".toUTF8) #[0x45, 0x48, 0x65, 0x6c, 0x6c, 0x6f]

#eval ser_de (Ipld.array #[Ipld.string "Hello"])
#eval ser_is (Ipld.array #[Ipld.string "Hello"]) #[0x81, 0x65, 0x48, 0x65, 0x6c, 0x6c, 0x6f]

#eval ser_de (Ipld.object (RBNode.singleton "Hello" (Ipld.string "World")))
#eval ser_is (Ipld.object (RBNode.singleton "Hello" (Ipld.string "World")))
  #[0xa1, 0x65, 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x65, 0x57, 0x6f, 0x72, 0x6c, 0x64]

def cid_ex : Cid := { version := 1, codec := 0x71, hash := (Multihash.sha3_256 (serialize Ipld.null)) }

-- from sp-ipld rust lib
def cid_ex_encoded : Array UInt8 := #[216, 42, 88, 37, 0, 1, 113, 22, 32, 69, 122, 165, 228, 28, 115, 252, 178, 178, 165, 119, 247, 73, 0, 207, 105, 172, 208, 72, 59, 220, 98, 86, 108, 23, 111, 21, 55, 76, 252, 185, 161]

#eval serialize (Ipld.link cid_ex)
#eval ser_is (Ipld.link cid_ex) cid_ex_encoded

#eval ser_de (Ipld.link cid_ex)
#eval deserialize (serialize (Ipld.link cid_ex))

structure Case where
  ipld: Ipld
  bytes: ByteArray

instance : ToString Case where
  toString case := s!"{Multibase.encodeBytes Multibase.Base16 case.bytes}"

/-- Test that a given test-case passes -/
def testCase (case : Case) : Bool := 
  deserialize (serialize case.ipld) == Except.ok case.ipld &&
  (serialize case.ipld) == case.bytes

def findFailing (cases: List Case) : List Case :=
  List.filter (fun x => not (testCase x)) cases

def cases : List Case := 
  [ Case.mk Ipld.null (ByteArray.mk #[246])
  , Case.mk (Ipld.bool true) (ByteArray.mk #[245])
  , Case.mk (Ipld.bool false) (ByteArray.mk #[244])
  , Case.mk (Ipld.number 0) (ByteArray.mk #[0])
  , Case.mk (Ipld.number 0x17) (ByteArray.mk #[23])
  , Case.mk (Ipld.number 0x18) (ByteArray.mk #[24,24])
  , Case.mk (Ipld.number 0xff) (ByteArray.mk #[24,255])
  , Case.mk (Ipld.number 0x100) (ByteArray.mk #[25,1,0])
  , Case.mk (Ipld.number 0xffff) (ByteArray.mk #[25,255,255])
  , Case.mk (Ipld.number 0x10000) (ByteArray.mk #[26,0,1,0,0])
  , Case.mk (Ipld.number 0xffffffff) (ByteArray.mk #[26,255,255,255,255])
  , Case.mk (Ipld.number 0x100000000) (ByteArray.mk #[27, 0,0,0,1,0,0,0,0])
  , Case.mk (Ipld.string "Hello") (ByteArray.mk #[0x65, 0x48, 0x65, 0x6c, 0x6c, 0x6f])
  , Case.mk (Ipld.bytes "Hello".toUTF8) (ByteArray.mk #[0x45, 0x48, 0x65, 0x6c, 0x6c, 0x6f])
  , Case.mk (Ipld.array #[Ipld.string "Hello"]) (ByteArray.mk #[0x81, 0x65, 0x48, 0x65, 0x6c, 0x6c, 0x6f])
  , Case.mk (Ipld.object (RBNode.singleton "Hello" (Ipld.string "World")))
    (ByteArray.mk #[0xa1, 0x65, 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x65, 0x57, 0x6f, 0x72, 0x6c, 0x64])
  ]

#eval findFailing cases
