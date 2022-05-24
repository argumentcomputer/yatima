import Yatima.YatimaSpec
import Yatima.Ipld.DagCbor

structure Case where
  ipld: Ipld
  bytes: ByteArray

instance : BEq (Except DeserializeError Ipld) where
  beq
  | Except.ok x, Except.ok y => x == y
  | Except.error x, Except.error y => x == y
  | _, _ => false

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
  , Case.mk (Ipld.object (Std.RBNode.singleton "Hello" (Ipld.string "World")))
    (ByteArray.mk #[0xa1, 0x65, 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x65, 0x57, 0x6f, 0x72, 0x6c, 0x64])
  ]

test_suite
  it "serializes and deserializes IPLD types" so findFailing cases should be empty
