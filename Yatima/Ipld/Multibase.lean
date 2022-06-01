import Yatima.Ipld.Utils
import Yatima.Ipld.MultibaseImpl

/-- An instance of the Multibase specification for a given base `β` -/
class Multibase (β: Type) where
  code         : Char
  alpha        : String
  digit        : Nat → Char
  read         : Char → Option Nat
  rfc4648      : Bool
  pad          : Bool

namespace Multibase
-- We define associated functions derived from the class in the same namespace
-- Ideally there would be a way to make `β` implicit and inferrable
variable (β: Type)
def zero [Multibase β]: Char := (alpha β)[0]
def base [Multibase β]: Nat  := (alpha β).length
def log2Base [Multibase β]: Nat  := Nat.log2' (base β)

-- Every RFC4648 base has a group size which is least-common-multiple of the
-- number of bits per digit of the base (`log2Base`) and 8 (the number of bits
-- per byte). This function returns the size of the group in bits.
def group [Multibase β] : Nat :=
  let x := (log2Base β)
  if x % 8 == 0 then x else
  if x % 4 == 0 then x * 2 else
  if x % 2 == 0 then x * 4 else
  x * 8

-- This is a little slow. We gain some in-kernel performance by
-- requiring Multibase instances to hardcode a `digit` function, even though
-- semantically it's derivable from `alpha`
def digit' [Multibase β] (i : Nat) : Char :=
  if i >= (alpha β).length then zero β else String.get (alpha β) ⟨i⟩

-- This is very slow because of the String.posOf call. We can't reduce
-- encodings in-kernel unless we hardcode the `read` function in the instance
def read' [Multibase β] (c: Char) : Option Nat :=
 let x := String.posOf (alpha β) c
 if x == (alpha β).endPos then none else some x.byteIdx

def validDigit [Multibase β] (x: Char): Bool := (read β x) != Option.none
def validate [Multibase β] (x: String): Bool := List.all x.data (validDigit β)

-- The core encoding function operates over `Nat` (GMP numbers) which is
-- supported in the Lean Kernel, thus allowing more complex static checking
-- compared to ByteArray operations (which are currently unsupported).,
def toStringCore [Multibase β] : Nat → Nat → String → String
| 0,        n, str => str
| fuel + 1, 0, str => str
| fuel + 1, n, str =>
  let dig := (digit β (n % (base β)))
  toStringCore fuel (n / (base β)) (String.append (String.singleton dig) str)

def toString [m: Multibase β] (x: List UInt8): String :=
  match Nat.fromByteListBE x with
  | 0 => ""
  | n => toStringCore β (n+1) n ""

def padRight (input: String) : Nat → String
| 0 => input
| n+1 => padRight (String.push input '=') n

def leadingZeroBitsCore : Nat → List UInt8 → Nat → Nat
| 0, bytes, n => n
| fuel+1, [], n => n
| fuel+1, 0::bs, n => leadingZeroBitsCore fuel bs (n + 8)
| fuel+1, b::bs, n => n + (8 - Nat.sigBits (UInt8.toNat b))

def leadingZeroBits (bytes: List UInt8) : Nat :=
  leadingZeroBitsCore (bytes.length) bytes 0

def encode [Multibase β] (x: List UInt8): String :=
  let log := log2Base β                        -- number of bits per digit
  let lzs := leadingZeroBits x                 -- count leading zero bits
  let rfc := rfc4648 β                         -- RFC4648 conformance
  let zeros := String.mk $ if rfc              -- if in RFC4648
    then List.replicate (lzs / log) (zero β)   -- left zeros are normal digits
    else List.replicate (lzs / 8) (zero β)     -- else, they count whole bytes
  let grp := group β / 8                       -- RFC group size in bytes
  let bytePad := (grp - x.length % grp) % grp  -- for counting right pad bytes
  let x := if rfc                              -- in RFC4648,
    then x ++ List.replicate bytePad 0         -- push right zero byte pad
    else x                                     -- else, do nothing
  let n := Nat.fromByteListBE x                -- convert bytes to big number
  let str := (toStringCore β (n+1) n "")       -- core conversion loop
  let charPad := ((bytePad * 8) / log)         -- the pad size in characters
  let str' := if rfc                           -- in RFC4648
    then str.dropRight charPad                 -- drop the character pad size
    else str                                   -- else, do nothing
  let str' := if rfc && pad β                  -- in RFC4648 with explicit pad
    then padRight str' charPad                 -- add back the pad characters
    else str'                                  -- else, do nothing
  String.singleton (code β) ++ zeros ++ str'   -- return w/ base code & zeros

def fromPad [Multibase β] : Nat → Nat → Nat → String → Option (Nat × Nat)
| 0, pad, acc, input => Option.some (pad, acc)
| fuel+1, pad, acc, "" => Option.some (pad, acc)
| fuel+1, pad, acc, input =>
  if (input[0] == '=')
  then fromPad fuel (pad+1) (acc * (base β)) (String.drop input 1)
  else Option.none

def fromStringCore [Multibase β] : Nat → Nat → String → Option (Nat × Nat)
| 0, acc, input => Option.some (0, acc)
| fuel+1, acc, "" => Option.some (0, acc)
| fuel+1, acc, input =>
  let c := input[0]
  if some c == '='
  then (fromPad β (fuel+1) 0 acc input)
  else Option.bind (read β input[0]) (fun d =>
    fromStringCore fuel (acc * (base β) + d) (String.drop input 1))

def fromString [m : Multibase β]: String → Option (List UInt8)
| "" => some []
| s  => (fun (x,y) => Nat.toByteListBE y) <$>
  (fromStringCore β (s.length) 0 s)

def readCode [m : Multibase β]: String → Option String
| ⟨c::cs⟩ => if c == code β
  then some (String.mk cs)
  else none
| _ => none

def readZeros [m : Multibase β]: List Char → Nat
| c::cs => if c == zero β
  then 1 + readZeros cs
  else 0
| _ => 0

def decode [Multibase β] (input : String): Option (List UInt8) :=
  Option.bind (readCode β input) $ fun x =>
  let len := x.length
  let zeroChars := readZeros β x.data
  let log := log2Base β
  let x := if rfc4648 β
    then
      -- Every rfc4648 base has a "group", e.g. 5 bytes or 40 bits for Base32
      -- which is is the least common multiple of 8 and the bits per base char
      -- This is so the characters and bytes line up evenly, and padding is
      -- introduced when there are insufficient input bits to fill a group.
      let grp     := group β                   -- bits per group
      let chars   := grp / log                 -- chars per group
      let inBits  := len * log                 -- bits in input
      let remBits := inBits % grp              -- excess input bits
      let pad     := (grp - remBits) / log     -- chars to fill a group
      let pad     := pad % chars               -- but don't fill an extra one
      padRight x pad
    else x
  if x = ""
  then Option.some []
  else Option.bind (fromStringCore β (x.length) 0 x) $ fun (padLen, x') =>
  let out    := Nat.toByteListBE x'
  let len    := if pad β then len else len + padLen
  let zeros := if rfc4648 β
    -- In RFC4648, leading zero chars correspond to log2Base β leading bits.
    -- Since the leading significant byte can contain leading zeros bits
    -- we have to check if the bits of the zeroChars and the decoded bytes
    -- don't have enough bits to cover the size of the input
    then if len * log > out.length * 8 + zeroChars * log
      then (zeroChars * log) / 8 + 1
      else (zeroChars * log) / 8
    -- outside of RFC4648, then a leading zero char *is* a leading zero byte
    else zeroChars
  let padBytes := if ((padLen * log) % 8) == 0
    then padLen * log / 8
    else ((padLen * log) / 8) + 1
  --let x''    := Nat.toByteListBE x'
  let zeros : List UInt8 := List.replicate zeros 0
  some (zeros ++ (List.take (out.length - padBytes) out))
  --s!"{len * log}, {Nat.log2' x'}, {zeroChars}, {zeros}, {(zeroChars' ++ (List.take (out.length - padBytes) out))}"

--/-- Top level multibase encoding function -/
def encodeBytes [Multibase β] (input: ByteArray) : String :=
  encode β input.data.data

--/-- Top level multibase decoding function -/
def decodeBytes [Multibase β] (x: String) : Option ByteArray :=
  ByteArray.mk <$> Array.mk <$> Multibase.decode β x

structure Base2
structure Base8
structure Base10
structure Base16
structure Base16Upper
structure Base32Hex
structure Base32HexUpper
structure Base32HexPad
structure Base32HexPadUpper
structure Base32
structure Base32Upper
structure Base32Pad
structure Base32PadUpper
structure Base32Z
structure Base36
structure Base36Upper
structure Base58BTC
structure Base58Flickr
structure Base64
structure Base64Pad
structure Base64URL
structure Base64URLPad

instance : Multibase Base2 where
  code := '0'
  alpha := "01"
  digit := digitBase2
  read := readBase2
  -- This seems not completely right given the multiformats base2 rfc
  rfc4648 := true
  pad := false

instance : Multibase Base8 where
  code := '7'
  alpha: String := "01234567"
  digit := digitBase8
  read := readBase8
  rfc4648 := true
  pad := false

instance : Multibase Base10 where
  code := '9'
  alpha: String := "0123456789"
  digit := digitBase10
  read := readBase10
  rfc4648 := false
  pad := false

instance : Multibase Base16 where
  code := 'f'
  alpha: String := "0123456789abcdef"
  digit := digitBase16
  read := readBase16
  rfc4648 := true
  pad := false

instance : Multibase Base16Upper where
  code := 'F'
  alpha: String := "0123456789ABCDEF"
  digit := digitBase16Upper
  read := readBase16
  rfc4648 := true
  pad := false

instance : Multibase Base32Hex where
  code := 'v'
  alpha: String := "0123456789abcdefghijklmnopqrstuv"
  digit := digitBase32Hex
  read := readBase32Hex
  rfc4648 := true
  pad := false

instance : Multibase Base32HexUpper where
  code := 'V'
  alpha: String := "0123456789ABCDEFGHIJKLMNOPQRSTUV"
  digit := digitBase32HexUpper
  read := readBase32Hex
  rfc4648 := true
  pad := false

instance : Multibase Base32HexPad where
  code := 't'
  alpha: String := "0123456789abcdefghijklmnopqrstuv"
  digit := digitBase32Hex
  read := readBase32Hex
  rfc4648 := true
  pad := true

instance : Multibase Base32HexPadUpper where
  code := 'T'
  alpha: String := "0123456789ABCDEFGHIJKLMNOPQRSTUV"
  digit := digitBase32HexUpper
  read := readBase32Hex
  rfc4648 := true
  pad := true

instance : Multibase Base32 where
  code := 'b'
  alpha: String := "abcdefghijklmnopqrstuvwxyz234567"
  digit := digitBase32
  read := readBase32
  rfc4648 := true
  pad := false

instance : Multibase Base32Upper where
  code := 'B'
  alpha: String := "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"
  digit := digitBase32Upper
  read := readBase32
  rfc4648 := true
  pad := false

instance : Multibase Base32Pad where
  code := 'c'
  alpha: String := "abcdefghijklmnopqrstuvwxyz234567"
  digit := digitBase32
  read := readBase32
  rfc4648 := true
  pad := true

instance : Multibase Base32PadUpper where
  code := 'C'
  alpha: String := "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"
  digit := digitBase32Upper
  read := readBase32
  rfc4648 := true
  pad := true

instance : Multibase Base32Z where
  code := 'h'
  alpha: String := "ybndrfg8ejkmcpqxot1uwisza345h769"
  digit := digitBase32Z
  read := readBase32Z
  rfc4648 := true
  pad := false

instance : Multibase Base36 where
  code := 'k'
  alpha: String := "0123456789abcdefghijklmnopqrstuvwxyz"
  digit := digitBase36
  read := readBase36
  rfc4648 := false
  pad := false

instance : Multibase Base36Upper where
  code := 'K'
  alpha: String := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  digit := digitBase36Upper
  read := readBase36
  rfc4648 := false
  pad := false

instance : Multibase Base58Flickr where
  code := 'Z'
  alpha: String := 
    "123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ"
  digit := digitBase58Flickr
  read := readBase58Flickr
  rfc4648 := false
  pad := false

instance : Multibase Base58BTC where
  code := 'z'
  alpha: String := 
    "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
  digit := digitBase58BTC
  read := readBase58BTC
  rfc4648 := false
  pad := false

instance : Multibase Base64 where
  code := 'm'
  alpha: String := 
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
  digit := digitBase64
  read := readBase64
  rfc4648 := true
  pad := false

instance : Multibase Base64Pad where
  code := 'M'
  alpha: String := 
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
  digit := digitBase64
  read := readBase64
  rfc4648 := true
  pad := true

instance : Multibase Base64URL where
  code := 'u'
  alpha: String := 
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
  digit := digitBase64URL
  read := readBase64URL
  rfc4648 := true
  pad := false

instance : Multibase Base64URLPad where
  code := 'U'
  alpha: String := 
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
  digit := digitBase64URL
  read := readBase64URL
  rfc4648 := true
  pad := true

end Multibase
