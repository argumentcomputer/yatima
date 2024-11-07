prelude
-- import YatimaStdLib.List
import yTypeChecker.Utils.YSL.UInt

namespace ByteArray

/-- Read Nat from Little-Endian ByteArray -/
def asLEtoNat (b : ByteArray) : Nat :=
  b.data.data.enum.foldl (init := 0)
    fun acc (i, bᵢ) => acc + bᵢ.toNat.shiftLeft (i * 8)

/-- Read Nat from Big-Endian ByteArray -/
def asBEtoNat (b : ByteArray) : Nat :=
  b.data.data.foldl (init := 0) fun acc bᵢ => acc.shiftLeft 8 + bᵢ.toNat

-- /-- Returns the index of -/
-- def leadingZeroBits (bytes : ByteArray) : Nat := Id.run do
--   let mut c := 0
--   for byte in bytes do
--     let zs := 8 - byte.toNat.sigBits
--     if byte != 0
--     then return c + zs
--     else c := c + zs
--   return c

/-- Appends `n` bytes of `0`s to a `ByteArray` -/
def pushZeros (bytes : ByteArray) (n : Nat) : ByteArray :=
  bytes ++ ⟨.mkArray n 0⟩

def beqL (a b : ByteArray) : Bool :=
  a.data == b.data

-- @[extern "lean_byte_array_beq"]
def beq : @& ByteArray → @& ByteArray → Bool :=
  beqL

-- def ordL (a b : ByteArray) : Ordering :=
--   compare a.data.data b.data.data

-- @[extern "lean_byte_array_ord"]
-- def ord : @& ByteArray → @& ByteArray → Ordering :=
--   ordL

instance : BEq ByteArray := ⟨ByteArray.beq⟩
-- instance : Ord ByteArray := ⟨ByteArray.ord⟩

instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue h₁  => isTrue $ congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse $ fun h => by cases h; exact (h₂ rfl)

def Subarray.asBA (s : Subarray UInt8) : ByteArray :=
  s.array.data.toByteArray

-- def toString (bs : ByteArray) : String := Id.run do
--   if bs.isEmpty then "b[]" else
--   let mut ans := "b["
--   for u in bs do
--     ans := ans ++ UInt8.showBits u ++ ","
--   return ans.dropRight 1 ++ "]"

-- def toHexString (bs : ByteArray) : String := Id.run do
--   if bs.isEmpty then "b[]" else
--   let mut ans := "b["
--   for u in bs do
--     ans := ans ++ UInt8.toHexString u ++ ", "
--   return ans.dropRight 2 ++ "]"

instance : Repr ByteArray where
  reprPrec bs _ := toString bs

def padLeft (bs : ByteArray) (u : UInt8) : Nat → ByteArray
  | 0 => bs
  | n + 1 => ByteArray.mk #[u] ++ padLeft bs u n

def getD (bs : ByteArray) (idx : Nat) (defaultValue : UInt8) : UInt8 :=
  bs.data.getD idx defaultValue

def getBit (bs : ByteArray) (n : Nat) : Bit :=
  let (idx, rem) := (n / 8, n % 8)
  UInt8.getBit (getD bs idx 0) rem

/--
Shifts the byte array left by 1 bit, preserves length (so in particular kills the
first coefficient
-/
def shiftLeft (bs : ByteArray) : ByteArray := Id.run do
  let mut answer : ByteArray := .mkEmpty bs.size
  for idx in [:bs.size] do
    answer := answer.push <|
      (getD bs idx 0 <<< 1 : UInt8) + (getD bs (idx + 1) 0 >>> 7 : UInt8)
  answer

/-- Shift the `ByteArray` right by `n` bytes by prepending the `n`-length array of `0`s -/
def shiftRight8n (bs : ByteArray) (n : Nat) := ⟨.mkArray n 0⟩ ++ bs

def shiftAdd (bs : ByteArray) (b : Bit) : ByteArray :=
  let ans := shiftLeft bs
  ans.set! (ans.size - 1) ((getD ans (ans.size - 1) 0) + b.toUInt8)

def sliceL (bs : ByteArray) (i n : Nat) : ByteArray :=
  let rec aux (acc : Array UInt8) : Nat → List UInt8 → Array UInt8
    | 0, _ => acc
    | n, [] => acc ++ (.mkArray n 0)
    | n + 1, b :: bs => aux (acc.push b) n bs
  .mk $ aux #[] n (bs.data.data.drop i)

@[extern "lean_byte_array_slice"]
def slice : @& ByteArray → Nat → Nat → ByteArray :=
  sliceL

theorem sliceL.aux_size : (sliceL.aux acc n bs).size = acc.size + n := by
  induction bs generalizing acc n
  · induction n
    · simp only [aux, Nat.add_zero]
    · simp only [aux, mkArray, Nat.succ_eq_add_one, Array.append, Array.size]
      simp only [Array.append_data, List.length_append, Array.data_length, List.length_replicate] -- TODO: Clean up this mess at some point
  rename_i ih
  cases n
  · simp [sliceL.aux]
  simp [sliceL.aux, ByteArray.size, ih]
  rw [Nat.add_assoc, Nat.add_comm 1 _]

theorem slice_size : (slice bytes i n).size = n := by
  simp [slice, sliceL, sliceL.aux, sliceL.aux_size, ByteArray.size]

theorem set_size : (set arr i u).size = arr.size := by
  simp [size, set]

theorem set!_size : (set! arr i u).size = arr.size := by
  simp [size, set!, Array.set!, Array.setD]
  by_cases h : i < arr.data.size <;> simp [h]

/-
In this section we define Arithmetic on ByteArrays viewed as natural numbers encoded in
little-endian form
-/

section arithmetic

def uInt8OverFlowMul (u₁ u₂ : UInt8) : UInt8 × UInt8 :=
  let u16 := u₁.toUInt16 * u₂.toUInt16
  (u16 >>> 8 |>.toUInt8, u16.toUInt8)

private def uInt8OverFlowAdd (u₁ u₂ : UInt8) : UInt8 × UInt8 :=
  let u16 := u₁.toUInt16 + u₂.toUInt16
  (u16 >>> 8 |>.toUInt8, u16.toUInt8)

def uInt8Mul (x : ByteArray) (u : UInt8) : ByteArray := Id.run do
  let mut carry: UInt8 := 0
  let mut answer: ByteArray := default

  for uX in x do
    let (carry1, res') := uInt8OverFlowMul uX u
    let (carry2, res) := uInt8OverFlowAdd carry res'
    answer := answer.push res
    carry := carry1 + carry2

  answer := if carry == 0 then answer else answer.push carry
  return answer

instance : HMul ByteArray UInt8 ByteArray where
  hMul := uInt8Mul

-- def add (x y : ByteArray) : ByteArray := Id.run do
--   let mut res := default
--   let mut cin := 0
--   let n := max x.size y.size

--   for i in [0 : n] do
--     let (r, o) := UInt8.sum3 cin (x.getD i 0) (y.getD i 0)
--     res := res.push r
--     cin := o

--   res := if cin == 0 then res else res.push cin
--   return res

-- instance : Add ByteArray where
--   add := add

def sub (x y : ByteArray) : ByteArray := Id.run do
  let mut res := default
  let mut cin := 0
  let n := max x.size y.size

  for i in [0 : n] do
    let xi := x.getD i 0
    let yi := y.getD i 0
    if xi < yi + cin then
      let diff := (255 - yi - cin) + xi + 1
      res := res.push diff
      cin := 1 else
      let diff := xi - yi - cin
      res := res.push diff
      cin := 0

  return res

instance : Sub ByteArray where
  sub := sub

-- /-- "naiive" multiplication of two ByteArrays -/
-- def nmul (x y : ByteArray) : ByteArray := Id.run do
--   let mut answer: ByteArray := default
--   let mut idx := 0

--   for u in x do
--     let temp := y * u
--     answer := answer + temp.shiftRight8n idx
--     idx := idx + 1

--   answer

-- /-- Karatsuba multiplication of two ByteArrays -/
-- partial def kmul (x y : ByteArray) : ByteArray :=
--   let n := max x.size y.size
--   if n ≤ 8 then nmul x y else
--     let low := n / 2
--     let high := n - low
--     let xLow := x.slice 0 low
--     let yLow := y.slice 0 low
--     let xHigh := x.slice low high
--     let yHigh := y.slice low high
--     let xMid := xHigh + xLow
--     let yMid := yHigh + yLow
--     let lowMul := kmul xLow yLow
--     let highMul := kmul xHigh yHigh
--     let midMul := kmul xMid yMid - highMul - lowMul
--     highMul.shiftRight8n (2 * high) + midMul.shiftRight8n high + lowMul

-- instance : Mul ByteArray where
--   mul := kmul

end arithmetic

end ByteArray
