prelude
import yTypeChecker.Utils.YSL.Bit

namespace UInt8

def showBits (u : UInt8) : String :=
  let numStr := u.toNat |> Nat.toDigits 2
  "".pushn '0' (8 - numStr.length) ++ ⟨numStr⟩

def toHexString (n : UInt8) : String :=
  let toLetter
    | 10 => "a"
    | 11 => "b"
    | 12 => "c"
    | 13 => "d"
    | 14 => "e"
    | 15 => "f"
    | n => toString n
  "0x" ++ toLetter (n / 16) ++ toLetter (n % 16)

def getBit (u : UInt8) (n : Nat) : Bit :=
  if u &&& (1 <<< (7 - n)).toUInt8 == 0 then .zero else .one

/-- sums up two u8's and returns the result and the cout -/
def sum2 (a b : UInt8) : UInt8 × UInt8 :=
  (a + b, if b <= 255 - a then 0 else 1)

/-- sums up three u8's and returns the result and the cout -/
def sum3 (i a b : UInt8) : UInt8 × UInt8 :=
  let (a', o₁) := sum2 i a
  let (b', o) := sum2 a' b
  (b', o + o₁)

end UInt8

def UInt16.toByteArrayL (n : UInt16) : ByteArray :=
  ⟨#[n.toUInt8, (n >>> 8) |>.toUInt8]⟩

@[extern "lean_uint16_to_byte_array"]
def UInt16.toByteArray : UInt16 → ByteArray :=
  UInt16.toByteArrayL

theorem UInt16.toByteArray_size_2 : (UInt16.toByteArray n).size = 2 := by
  simp [ByteArray.size, Array.size, List.length]

def UInt32.toByteArrayL (n : UInt32) : ByteArray :=
  let a₀ := n.toUInt8
  let n := n >>> 8
  let a₁ := n |>.toUInt8
  let n := n >>> 8
  let a₂ := n |>.toUInt8
  let n := n >>> 8
  let a₃ := n |>.toUInt8
  ⟨#[a₀, a₁, a₂, a₃]⟩

@[extern "lean_uint32_to_byte_array"]
def UInt32.toByteArray : UInt32 → ByteArray :=
  UInt32.toByteArrayL

theorem UInt32.toByteArray_size_4 : (UInt32.toByteArray n).size = 4 := by
  simp [ByteArray.size, Array.size, List.length]

def UInt64.toByteArrayL (n : UInt64) : ByteArray :=
  let a₀ := n.toUInt8
  let n := n >>> 8
  let a₁ := n |>.toUInt8
  let n := n >>> 8
  let a₂ := n |>.toUInt8
  let n := n >>> 8
  let a₃ := n |>.toUInt8
  let n := n >>> 8
  let a₄ := n |>.toUInt8
  let n := n >>> 8
  let a₅ := n |>.toUInt8
  let n := n >>> 8
  let a₆ := n |>.toUInt8
  let n := n >>> 8
  let a₇ := n |>.toUInt8
  ⟨#[a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇]⟩

@[extern "lean_uint64_to_byte_array"]
def UInt64.toByteArray : UInt64 → ByteArray :=
  UInt64.toByteArrayL

theorem UInt64.toByteArray_size_8 : (UInt64.toByteArray n).size = 8 := by
  simp [ByteArray.size, Array.size, List.length]
