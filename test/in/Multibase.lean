import Yatima.Ipld.Multibase

open Multibase

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
    s!"{case.bytes} {if case.read then "<-" else "<->"} {case.string}"

def findFailing (cases: List Case) : List Case :=
  List.filter (fun x => not (testCase x)) cases

namespace Basic

#eval "yes mani !".toUTF8
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

#eval findFailing cases

end Basic

namespace CaseInsensitivity

#eval "hello world".toUTF8
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

#eval findFailing cases

end CaseInsensitivity

namespace LeadingZero
-- leading_zero.csv
#eval "\x00yes mani !".toUTF8
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

#eval findFailing cases

end LeadingZero

namespace TwoLeadingZeros

#eval "\x00\x00yes mani !".toUTF8
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

#eval findFailing cases

end TwoLeadingZeros

namespace RFC4648
-- RFC4648 Test Vectors: https://datatracker.ietf.org/doc/html/rfc4648#section-10
-- test vector `i` is the first `i` letters of the string "foobar" as UTF8
#eval "foobar".toUTF8
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

#eval findFailing cases

end RFC4648
