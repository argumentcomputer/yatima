import Yatima.YatimaSpec
import Yatima.Ipld.Multihash
import Yatima.Ipld.Multibase
import Yatima.Ipld.DagCbor
import Yatima.Ipld.UnsignedVarInt

open Std (RBNode)

namespace MH

structure Case where
  input: ByteArray
  hash: Multihash

/-- Test that a given test-case passes -/
def testCase (case : Case) : Bool := 
  let hash := Multihash.sha3_512 case.input
  hash == case.hash &&
  Multihash.fromBytes (Multihash.toBytes hash) == some hash

def findFailing (cases: List Case) : List Case :=
  List.filter (fun x => not (testCase x)) cases

def mkCase (input: String) (hash: String) : Option Case := do
  let input ← input.toUTF8
  let hash  ← ByteArray.mk <$> Array.mk <$> Multibase.decode Multibase.Base16 hash
  let hash  ← Multihash.fromBytes hash
  return Case.mk input hash

def cases : List Case := List.catOptions
  [ mkCase "431fb5d4c9b735ba1a34d0df045118806ae2336f2c" "f14409a7a8207a57d03e9c524ae7fd39563bfe1a466a3a0323875eba8b034a1d59c3b7218103543f7777f17ef03dcaf44d12c74dfb83726e7425cf61225e9a54b3b3a"
  , mkCase "2d6db2d7882fa8b7d56e74b8e24036deb475de8c94" "f1440968e697b2d5e92470002f9e59e13557f47b895dc9c79082a90e91515f025563773aec0f70219c87350c79707de67500866d7fe084c5316e12c6930949b28865d"
  , mkCase "6c00022ba29d15926c4580332ded091e666f0ec5d9" "f144047f57e2056010afa03bc58141ba3754f41917518c81711236eaca3766e333b9a2a767a90363f7a179e776d85aa6610713709ee46531f9a454565f737c68bdc56"
  , mkCase "1391551dc8f15110d256c493ed485bca8cfed07241" "f144089c62811bc2d3fec81631112ad9f03de23d065697f758b8df9e5d791474ab2f20ddac684c23b203b730be465a5d0f06b76e9dbc48590def7d58e96d93b4e0418"
  , mkCase "557f47c855a5ca40daa3c0904a1e43647b4021ce0c" "f1440a7ab209784597d2e251860e2464c04c386c4887af778136414c80d7c643ccd3b2a0b61e31986a79ef8e4fdd41601fbe7c982c132df4bc77ecc2e27d3edd55f90"
  , mkCase "4c44254356730838195a32cbb1b8be3bed4c6c05c0" "f14403dc43b479f5e9e008a5256ca442e66286995c39deb732a6fb4e2e791a3c4a6a6e5322e571e945a78748896edc67866ab00c767320f6956833857eab991a73a77"
  ]

end MH

namespace MB

structure Case where
  read: Bool
  β : Type
  inst : Multibase β
  bytes: List UInt8
  string : String

/-- Make a test-case for checking that `case.bytes` encodes to `case.string`
    and that string `y` decodes to `case.bytes` -/
def mkCase (β : Type) [inst: Multibase β] (x: List UInt8) (y: String) : Case
  := Case.mk false β inst x y

/-- Make a test-case for checking that string `y` decodes to `case.bytes`,
    but where `case.bytes` might not encode to `case.string` -/
def mkReadCase (β : Type) [inst: Multibase β] (x: List UInt8) (y: String) : Case
  := Case.mk true β inst x y

/-- Test that a given test-case passes -/
def testCase (case : Case) : Bool := 
  let enc : String := (@Multibase.encode case.β case.inst case.bytes);
  (if case.read then true else enc == case.string)
  && (@Multibase.decode case.β case.inst enc == some case.bytes)

instance : ToString Case where
  toString case :=
    s!"{case.bytes} {if case.read then "←" else "↔"} {case.string}"

def findFailing (cases: List Case) : List Case :=
  List.filter (fun x => not (testCase x)) cases

namespace Basic

def basic : List UInt8 := [121, 101, 115, 32, 109, 97, 110, 105, 32, 33]

def cases : List Case :=
  [ mkCase Multibase.Base2 basic "001111001011001010111001100100000011011010110000101101110011010010010000000100001"
  , mkCase Multibase.Base8 basic             "7362625631006654133464440102"
  , mkCase Multibase.Base10 basic            "9573277761329450583662625"
  , mkCase Multibase.Base16 basic            "f796573206d616e692021"
  , mkCase Multibase.Base16 basic            "f796573206d616e692021"
  , mkCase Multibase.Base32Hex basic         "vf5in683dc5n6i811"
  , mkCase Multibase.Base32HexUpper basic    "VF5IN683DC5N6I811"
  , mkCase Multibase.Base32HexPad basic      "tf5in683dc5n6i811"
  , mkCase Multibase.Base32HexPadUpper basic "TF5IN683DC5N6I811"
  , mkCase Multibase.Base32 basic            "bpfsxgidnmfxgsibb"
  , mkCase Multibase.Base32Upper basic       "BPFSXGIDNMFXGSIBB"
  , mkCase Multibase.Base32Pad basic         "cpfsxgidnmfxgsibb"
  , mkCase Multibase.Base32PadUpper basic    "CPFSXGIDNMFXGSIBB"
  , mkCase Multibase.Base32Z basic           "hxf1zgedpcfzg1ebb"
  , mkCase Multibase.Base36 basic            "k2lcpzo5yikidynfl"
  , mkCase Multibase.Base36Upper basic       "K2LCPZO5YIKIDYNFL"
  , mkCase Multibase.Base58Flickr basic      "Z7Pznk19XTTzBtx"
  , mkCase Multibase.Base58BTC basic         "z7paNL19xttacUY"
  , mkCase Multibase.Base64 basic            "meWVzIG1hbmkgIQ"
  , mkCase Multibase.Base64Pad basic         "MeWVzIG1hbmkgIQ=="
  , mkCase Multibase.Base64URL basic         "ueWVzIG1hbmkgIQ"
  , mkCase Multibase.Base64URLPad basic      "UeWVzIG1hbmkgIQ=="
  ]

end Basic

namespace CaseInsensitivity

def hello : List UInt8 := [104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100]

def cases : List Case :=
 [ mkReadCase Multibase.Base16            hello "f68656c6c6f20776F726C64"
 , mkReadCase Multibase.Base16Upper       hello "F68656c6c6f20776F726C64"
 , mkReadCase Multibase.Base32            hello "bnbswy3dpeB3W64TMMQ"
 , mkReadCase Multibase.Base32Upper       hello "Bnbswy3dpeB3W64TMMQ"
 , mkReadCase Multibase.Base32Hex         hello "vd1imor3f41RMUSJCCG"
 , mkReadCase Multibase.Base32HexUpper    hello "Vd1imor3f41RMUSJCCG"
 , mkReadCase Multibase.Base32Pad         hello "cnbswy3dpeB3W64TMMQ======"
 , mkReadCase Multibase.Base32PadUpper    hello "Cnbswy3dpeB3W64TMMQ======"
 , mkReadCase Multibase.Base32HexPad      hello "td1imor3f41RMUSJCCG======"
 , mkReadCase Multibase.Base32HexPadUpper hello "Td1imor3f41RMUSJCCG======"
 , mkReadCase Multibase.Base36            hello "kfUvrsIvVnfRbjWaJo"
 , mkReadCase Multibase.Base36Upper       hello "KfUVrSIVVnFRbJWAJo"
 ]

end CaseInsensitivity

namespace LeadingZero
-- leading_zero.csv

def zero : List UInt8 := [0, 121, 101, 115, 32, 109, 97, 110, 105, 32, 33]

def cases : List Case :=
  [ mkCase Multibase.Base2  zero            "00000000001111001011001010111001100100000011011010110000101101110011010010010000000100001"
  , mkCase Multibase.Base8 zero             "7000745453462015530267151100204"
  , mkCase Multibase.Base10 zero            "90573277761329450583662625"
  , mkCase Multibase.Base16 zero            "f00796573206d616e692021"
  , mkCase Multibase.Base16Upper zero       "F00796573206D616E692021"
  , mkCase Multibase.Base32 zero            "bab4wk4zanvqw42jaee"
  , mkCase Multibase.Base32Upper zero       "BAB4WK4ZANVQW42JAEE"
  , mkCase Multibase.Base32Hex zero         "v01smasp0dlgmsq9044"
  , mkCase Multibase.Base32HexUpper zero    "V01SMASP0DLGMSQ9044"
  , mkCase Multibase.Base32Pad zero         "cab4wk4zanvqw42jaee======"
  , mkCase Multibase.Base32PadUpper zero    "CAB4WK4ZANVQW42JAEE======"
  , mkCase Multibase.Base32HexPad zero      "t01smasp0dlgmsq9044======"
  , mkCase Multibase.Base32HexPadUpper zero "T01SMASP0DLGMSQ9044======"
  , mkCase Multibase.Base32Z zero           "hybhskh3ypiosh4jyrr"
  , mkCase Multibase.Base36 zero            "k02lcpzo5yikidynfl"
  , mkCase Multibase.Base36Upper zero       "K02LCPZO5YIKIDYNFL"
  , mkCase Multibase.Base58Flickr zero      "Z17Pznk19XTTzBtx"
  , mkCase Multibase.Base58BTC zero         "z17paNL19xttacUY"
  , mkCase Multibase.Base64 zero            "mAHllcyBtYW5pICE"
  , mkCase Multibase.Base64Pad zero         "MAHllcyBtYW5pICE="
  , mkCase Multibase.Base64URL zero         "uAHllcyBtYW5pICE"
  , mkCase Multibase.Base64URLPad zero      "UAHllcyBtYW5pICE="
  ]

end LeadingZero

namespace TwoLeadingZeros

def zeros : List UInt8 := [0, 0, 121, 101, 115, 32, 109, 97, 110, 105, 32, 33]

def cases : List Case := 
  [ mkCase Multibase.Base2 zeros              "0000000000000000001111001011001010111001100100000011011010110000101101110011010010010000000100001"
  , mkCase Multibase.Base8 zeros              "700000171312714403326055632220041"
  , mkCase Multibase.Base10 zeros             "900573277761329450583662625"
  , mkCase Multibase.Base16 zeros             "f0000796573206d616e692021"
  , mkCase Multibase.Base16Upper zeros        "F0000796573206D616E692021"
  , mkCase Multibase.Base32 zeros             "baaahszltebwwc3tjeaqq"
  , mkCase Multibase.Base32Upper zeros        "BAAAHSZLTEBWWC3TJEAQQ"
  , mkCase Multibase.Base32Hex zeros          "v0007ipbj41mm2rj940gg"
  , mkCase Multibase.Base32HexUpper zeros     "V0007IPBJ41MM2RJ940GG"
  , mkCase Multibase.Base32Pad zeros          "caaahszltebwwc3tjeaqq===="
  , mkCase Multibase.Base32PadUpper zeros     "CAAAHSZLTEBWWC3TJEAQQ===="
  , mkCase Multibase.Base32HexPad zeros       "t0007ipbj41mm2rj940gg===="
  , mkCase Multibase.Base32HexPadUpper zeros  "T0007IPBJ41MM2RJ940GG===="
  , mkCase Multibase.Base32Z zeros            "hyyy813murbssn5ujryoo"
  , mkCase Multibase.Base36 zeros             "k002lcpzo5yikidynfl"
  , mkCase Multibase.Base36Upper zeros        "K002LCPZO5YIKIDYNFL"
  , mkCase Multibase.Base58Flickr zeros       "Z117Pznk19XTTzBtx"
  , mkCase Multibase.Base58BTC zeros          "z117paNL19xttacUY"
  , mkCase Multibase.Base64 zeros             "mAAB5ZXMgbWFuaSAh"
  , mkCase Multibase.Base64Pad zeros          "MAAB5ZXMgbWFuaSAh"
  , mkCase Multibase.Base64URL zeros          "uAAB5ZXMgbWFuaSAh"
  , mkCase Multibase.Base64URLPad zeros       "UAAB5ZXMgbWFuaSAh"
  ]

end TwoLeadingZeros

namespace RFC4648
-- RFC4648 Test Vectors: https://datatracker.ietf.org/doc/html/rfc4648#section-10
-- test vector `i` is the first `i` letters of the string "foobar" as UTF8

def rfc0 : List UInt8 := []
def rfc1 : List UInt8 := [102]
def rfc2 : List UInt8 := [102, 111]
def rfc3 : List UInt8 := [102, 111, 111]
def rfc4 : List UInt8 := [102, 111, 111, 98]
def rfc5 : List UInt8 := [102, 111, 111, 98, 97]
def rfc6 : List UInt8 := [102, 111, 111, 98, 97, 114]

def cases : List Case :=
  [ mkCase Multibase.Base16 rfc0  "f"
  , mkCase Multibase.Base16 rfc1  "f66"
  , mkCase Multibase.Base16 rfc2  "f666f"
  , mkCase Multibase.Base16 rfc3  "f666f6f"
  , mkCase Multibase.Base16 rfc4  "f666f6f62"
  , mkCase Multibase.Base16 rfc5  "f666f6f6261"
  , mkCase Multibase.Base16 rfc6  "f666f6f626172"
  , mkCase Multibase.Base16Upper rfc0 "F"
  , mkCase Multibase.Base16Upper rfc1 "F66"
  , mkCase Multibase.Base16Upper rfc2 "F666F"
  , mkCase Multibase.Base16Upper rfc3 "F666F6F"
  , mkCase Multibase.Base16Upper rfc4 "F666F6F62"
  , mkCase Multibase.Base16Upper rfc5 "F666F6F6261"
  , mkCase Multibase.Base16Upper rfc6 "F666F6F626172"
  , mkCase Multibase.Base32Hex rfc0 "v"
  , mkCase Multibase.Base32Hex rfc1 "vco"
  , mkCase Multibase.Base32Hex rfc2 "vcpng"
  , mkCase Multibase.Base32Hex rfc3 "vcpnmu"
  , mkCase Multibase.Base32Hex rfc4 "vcpnmuog"
  , mkCase Multibase.Base32Hex rfc5 "vcpnmuoj1"
  , mkCase Multibase.Base32Hex rfc6 "vcpnmuoj1e8"
  , mkCase Multibase.Base32HexUpper rfc0 "V"
  , mkCase Multibase.Base32HexUpper rfc1 "VCO"
  , mkCase Multibase.Base32HexUpper rfc2 "VCPNG"
  , mkCase Multibase.Base32HexUpper rfc3 "VCPNMU"
  , mkCase Multibase.Base32HexUpper rfc4 "VCPNMUOG"
  , mkCase Multibase.Base32HexUpper rfc5 "VCPNMUOJ1"
  , mkCase Multibase.Base32HexUpper rfc6 "VCPNMUOJ1E8"
  , mkCase Multibase.Base32HexPad rfc0 "t"
  , mkCase Multibase.Base32HexPad rfc1 "tco======"
  , mkCase Multibase.Base32HexPad rfc2 "tcpng===="
  , mkCase Multibase.Base32HexPad rfc3 "tcpnmu==="
  , mkCase Multibase.Base32HexPad rfc4 "tcpnmuog="
  , mkCase Multibase.Base32HexPad rfc5 "tcpnmuoj1"
  , mkCase Multibase.Base32HexPad rfc6 "tcpnmuoj1e8======"
  , mkCase Multibase.Base32HexPadUpper rfc0 "T"
  , mkCase Multibase.Base32HexPadUpper rfc1 "TCO======"
  , mkCase Multibase.Base32HexPadUpper rfc2 "TCPNG===="
  , mkCase Multibase.Base32HexPadUpper rfc3 "TCPNMU==="
  , mkCase Multibase.Base32HexPadUpper rfc4 "TCPNMUOG="
  , mkCase Multibase.Base32HexPadUpper rfc5 "TCPNMUOJ1"
  , mkCase Multibase.Base32HexPadUpper rfc6 "TCPNMUOJ1E8======"
  , mkCase Multibase.Base32 rfc0 "b"
  , mkCase Multibase.Base32 rfc1 "bmy"
  , mkCase Multibase.Base32 rfc2 "bmzxq"
  , mkCase Multibase.Base32 rfc3 "bmzxw6"
  , mkCase Multibase.Base32 rfc4 "bmzxw6yq"
  , mkCase Multibase.Base32 rfc5 "bmzxw6ytb"
  , mkCase Multibase.Base32 rfc6 "bmzxw6ytboi"
  , mkCase Multibase.Base32Upper rfc0 "B"
  , mkCase Multibase.Base32Upper rfc1 "BMY"
  , mkCase Multibase.Base32Upper rfc2 "BMZXQ"
  , mkCase Multibase.Base32Upper rfc3 "BMZXW6"
  , mkCase Multibase.Base32Upper rfc4 "BMZXW6YQ"
  , mkCase Multibase.Base32Upper rfc5 "BMZXW6YTB"
  , mkCase Multibase.Base32Upper rfc6 "BMZXW6YTBOI"
  , mkCase Multibase.Base32Pad rfc0 "c"
  , mkCase Multibase.Base32Pad rfc1 "cmy======"
  , mkCase Multibase.Base32Pad rfc2 "cmzxq===="
  , mkCase Multibase.Base32Pad rfc3 "cmzxw6==="
  , mkCase Multibase.Base32Pad rfc4 "cmzxw6yq="
  , mkCase Multibase.Base32Pad rfc5 "cmzxw6ytb"
  , mkCase Multibase.Base32Pad rfc6 "cmzxw6ytboi======"
  , mkCase Multibase.Base32PadUpper rfc0 "C"
  , mkCase Multibase.Base32PadUpper rfc1 "CMY======"
  , mkCase Multibase.Base32PadUpper rfc2 "CMZXQ===="
  , mkCase Multibase.Base32PadUpper rfc3 "CMZXW6==="
  , mkCase Multibase.Base32PadUpper rfc4 "CMZXW6YQ="
  , mkCase Multibase.Base32PadUpper rfc5 "CMZXW6YTB"
  , mkCase Multibase.Base32PadUpper rfc6 "CMZXW6YTBOI======"
  , mkCase Multibase.Base64 rfc0 "m"
  , mkCase Multibase.Base64 rfc1 "mZg"
  , mkCase Multibase.Base64 rfc2 "mZm8"
  , mkCase Multibase.Base64 rfc3 "mZm9v"
  , mkCase Multibase.Base64 rfc4 "mZm9vYg"
  , mkCase Multibase.Base64 rfc5 "mZm9vYmE"
  , mkCase Multibase.Base64 rfc6 "mZm9vYmFy"
  , mkCase Multibase.Base64Pad rfc0 "M"
  , mkCase Multibase.Base64Pad rfc1 "MZg=="
  , mkCase Multibase.Base64Pad rfc2 "MZm8="
  , mkCase Multibase.Base64Pad rfc3 "MZm9v"
  , mkCase Multibase.Base64Pad rfc4 "MZm9vYg=="
  , mkCase Multibase.Base64Pad rfc5 "MZm9vYmE="
  , mkCase Multibase.Base64Pad rfc6 "MZm9vYmFy"
  , mkCase Multibase.Base64URLPad rfc0 "U"
  , mkCase Multibase.Base64URLPad rfc1 "UZg=="
  , mkCase Multibase.Base64URLPad rfc2 "UZm8="
  , mkCase Multibase.Base64URLPad rfc3 "UZm9v"
  , mkCase Multibase.Base64URLPad rfc4 "UZm9vYg=="
  , mkCase Multibase.Base64URLPad rfc5 "UZm9vYmE="
  , mkCase Multibase.Base64URLPad rfc6 "UZm9vYmFy"
  ]
end RFC4648
end MB

namespace DC

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
  , Case.mk (Ipld.object (RBNode.singleton "Hello" (Ipld.string "World")))
    (ByteArray.mk #[0xa1, 0x65, 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x65, 0x57, 0x6f, 0x72, 0x6c, 0x64])
  ]

end DC

namespace UVI

structure Case where
  nat: Nat
  bytes: ByteArray

instance : ToString Case where
  toString case := s!"{case.nat} ↔ {case.bytes}"

/-- Test that a given test-case passes -/
def testCase (case : Case) : Bool := 
  match UnsignedVarInt.fromVarInt case.bytes with
  | Option.none => false
  | Option.some (n,_) =>
    UnsignedVarInt.toVarInt case.nat == case.bytes &&
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

end UVI

test_suite
  it "" so MH.findFailing MH.cases should be empty

  it "" so MB.findFailing MB.Basic.cases should be empty
  it "" so MB.findFailing MB.CaseInsensitivity.cases should be empty
  it "" so MB.findFailing MB.LeadingZero.cases should be empty
  it "" so MB.findFailing MB.TwoLeadingZeros.cases should be empty
  it "" so MB.findFailing MB.RFC4648.cases should be empty

  it "" so DC.findFailing DC.cases should be empty

  it "" so UVI.findFailing UVI.cases should be empty
