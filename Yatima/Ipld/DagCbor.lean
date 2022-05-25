import Yatima.Ipld.Ipld
import Yatima.Ipld.Multihash
import Std.Data.RBTree

namespace Yatima.DagCbor

open Std (RBNode RBMap)

def ser_null : ByteArray := ByteArray.mk #[0xf6]

def ser_bool : Bool → ByteArray
  | true  => ByteArray.mk #[0xf5]
  | false => ByteArray.mk #[0xf4]

def ser_u8 (major : UInt8) (n : UInt8) : ByteArray :=
  if n <= 0x17
  then ByteArray.mk #[((major.toNat.shiftLeft 5).lor n.toNat).toUInt8]
  else ByteArray.mk #[((major.toNat.shiftLeft 5).lor 24).toUInt8, n]

def ser_u16 (major : UInt8) (n : UInt16) : ByteArray :=
  if n <= 255
  then ser_u8 major n.toUInt8
  else
    let maj := ((major.toNat.shiftLeft 5).lor 25).toUInt8
    let buf := ByteArray.mk #[maj, 0, 0]
    let num := (n.toNat.toByteArrayBE)
    ByteArray.copySlice num 0 buf (buf.size - num.size) 2

def ser_u32 (major : UInt8) (n : UInt32) : ByteArray :=
  if n <= 65535
  then ser_u16 major n.toUInt16
  else
    let maj := ((major.toNat.shiftLeft 5).lor 26).toUInt8
    let buf := ByteArray.mk #[maj, 0, 0, 0, 0]
    let num := (n.toNat.toByteArrayBE)
    ByteArray.copySlice num 0 buf (buf.size - num.size) 4

def ser_u64 (major: UInt8) (n : UInt64) : ByteArray :=
  if n <= 4294967295
  then ser_u32 major n.toUInt32
  else
    let maj : UInt8 := ((major.toNat.shiftLeft 5).lor 27).toUInt8
    let buf := ByteArray.mk #[maj, 0, 0, 0, 0, 0, 0, 0, 0]
    let num := (n.toNat.toByteArrayBE)
    ByteArray.copySlice num 0 buf (buf.size - num.size) 8

def ser_string (s: String) : ByteArray :=
  let str_bytes := s.toUTF8
  (ser_u64 3 str_bytes.size.toUInt64).append str_bytes

def ser_bytes (b: ByteArray) : ByteArray :=
  ByteArray.append (ser_u64 2 b.size.toUInt64) b

def ser_link (l: Cid) : ByteArray :=
  let buf := Cid.toBytes l
  (ser_u64 6 42) ++ ser_u64 2 (buf.size.toUInt64 + 1) ++ ⟨#[0]⟩ ++ buf

def nodeToList (map : RBNode String (fun _ => Ipld)) : List (String × Ipld) := 
  map.revFold (fun as a b => (a,b)::as) []

-- TODO: Add termination_by measure to show that serialize does terminate
mutual

  partial def serialize : Ipld → ByteArray
    | Ipld.null     => ser_null
    | Ipld.bool   b => ser_bool b
    | Ipld.number n => ser_u64 0 n
    | Ipld.string s => ser_string s
    | Ipld.bytes  b => ser_bytes b
    | Ipld.array  a => ser_array a
    | Ipld.object o => ser_object o
    | Ipld.link cid => ser_link cid

  partial def ser_array (as: Array Ipld) : ByteArray :=
    as.foldl (init := ser_u64 4 as.size.toUInt64)
      fun acc a => acc ++ serialize a

  partial def ser_object (o: RBNode String (fun _ => Ipld)) : ByteArray :=
    let list := nodeToList o
    list.foldl (init := ser_u64 5 list.length.toUInt64)
      fun acc (k, v) => acc ++ ser_string k ++ serialize v

end

structure ByteCursor where
  bytes : ByteArray
  pos: Nat
  deriving Repr

inductive DeserializeError
  | UnexpectedEOF
  | NoAlt
  | UnknownCborTag (tag: UInt8)
  | UnexpectedCborCode (code: Nat)
  | CidLenOutOfRange (len: UInt8)
  | CidPrefix (tag: UInt8)
  | CidRead
  | ExpectedTag (tag: UInt8) (read: UInt8)
  deriving BEq, Repr

instance : ToString ByteCursor where
  toString bc := (toString bc.bytes.data.data) ++ "[" ++ (toString bc.pos) ++ "]"

instance : ToString DeserializeError where
  toString
  | DeserializeError.UnexpectedEOF => "Unexpected EOF"
  | DeserializeError.NoAlt => "No Alt"
  | DeserializeError.UnknownCborTag t => "Unknown Tag " ++ toString t
  | DeserializeError.UnexpectedCborCode t => "UnexpectedCborCode " ++ toString t
  | DeserializeError.CidRead => "CidRead"
  | DeserializeError.ExpectedTag t r => 
    "Expected Tag " ++ toString t ++ ", read " ++ toString r
  | DeserializeError.CidLenOutOfRange len => "CidLenOutOfRange " ++ toString len
  | DeserializeError.CidPrefix tag => "CidPrefix " ++ toString tag

def getPos (x: ByteCursor) : Nat := x.pos
def setPos (x: ByteCursor) (i: Nat) : ByteCursor := 
  { bytes := x.bytes, pos := i}

def Deserializer (α : Type): Type := EStateM DeserializeError ByteCursor α

instance : Monad Deserializer where
  bind     := EStateM.bind
  pure     := EStateM.pure
  map      := EStateM.map
  seqRight := EStateM.seqRight

instance : MonadStateOf ByteCursor Deserializer where
  set       := EStateM.set
  get       := EStateM.get
  modifyGet := EStateM.modifyGet

instance : MonadExceptOf DeserializeError Deserializer where
  throw    := EStateM.throw
  tryCatch := EStateM.tryCatch

def next : Deserializer UInt8 := do
  let { bytes, pos } ← get
  if pos + 1 > bytes.size then throw DeserializeError.UnexpectedEOF
  set (ByteCursor.mk bytes (pos + 1))
  return bytes[pos]

def take (n: Nat) : Deserializer ByteArray := do
  let { bytes, pos } ← get
  if pos + n > bytes.size then throw DeserializeError.UnexpectedEOF
  set (ByteCursor.mk bytes (pos + n))
  return bytes.extract pos (pos + n)

def tag (t: UInt8) : Deserializer UInt8 := do
  let tag ← next
  if t == tag
  then return tag
  else throw (DeserializeError.ExpectedTag t tag)

def alt {α : Type} (ds : List (Deserializer α)) : Deserializer α := do
  match ds with
  | [] => throw DeserializeError.NoAlt
  | c::cs => EStateM.orElse' c (alt cs)

def read_u8: Deserializer UInt8 := next

def read_u16: Deserializer UInt16 := do
  let bytes ← take 2
  return bytes.asBEtoNat.toUInt16

def read_u32: Deserializer UInt32 := do
  let bytes ← take 4
  return bytes.asBEtoNat.toUInt32

def read_u64: Deserializer UInt64 := do
  let bytes ← take 8
  return bytes.asBEtoNat.toUInt64

def read_bytes (len: Nat) : Deserializer ByteArray := take len

def read_str (len: Nat) : Deserializer String := do
  let bytes ← take len
  return String.fromUTF8Unchecked bytes

def repeat_for {α : Type} (len : Nat) (d : Deserializer α) :
    Deserializer (List α) := 
  match len with
  | 0 => return []
  | n+1 => List.cons <$> d <*> repeat_for n d

partial def repeat_il {α : Type} (d : Deserializer α) : Deserializer (List α) := do
  let {bytes, pos} ← get
  if bytes[pos] == 0xff
  then return []
  else List.cons <$> d <*> (repeat_il d)

def read_link : Deserializer Cid := do
  let ty ← read_u8
  if ty != 0x58 then throw (DeserializeError.UnknownCborTag ty)
  let len ← read_u8
  if len == 0 then throw (DeserializeError.CidLenOutOfRange len)
  let bytes ← (read_bytes len.toNat)
  if bytes[0] != 0 then throw (DeserializeError.CidPrefix bytes[0])
  let bytes := bytes.extract 1 bytes.size
  let cid := Cid.fromBytes bytes
  match cid with
  | Option.none => throw DeserializeError.CidRead
  | Option.some x => return x

def read_len : Nat → Deserializer Nat
| 0x18 => UInt8.toNat <$> read_u8
| 0x19 => UInt16.toNat <$> read_u16
| 0x1a => UInt32.toNat <$> read_u32
| 0x1b => UInt64.toNat <$> read_u64
| x => if x <= 0x17
  then return x
  else throw (DeserializeError.UnexpectedCborCode x)

def decode_string : Deserializer String := do
  let major ← read_u8
  if 0x60 <= major && major <= 0x7b
  then (read_len (major.toNat - 0x60)) >>= read_str
  else throw (DeserializeError.UnexpectedCborCode major.toNat)

partial def deserialize_ipld : Deserializer Ipld := do
let major ← read_u8
match major with
| 0x18 => Ipld.number <$> UInt8.toUInt64 <$> read_u8
| 0x19 => Ipld.number <$> UInt16.toUInt64 <$> read_u16
| 0x1a => Ipld.number <$> UInt32.toUInt64 <$> read_u32
| 0x1b => Ipld.number <$> read_u64
-- Negative
-- | 0x38 => Ipld.number <$> UInt8.toUInt64 <$> read_u8
-- | 0x39 => Ipld.number <$> UInt8.toUInt64 <$> read_u8
-- | 0x3a => Ipld.number <$> UInt8.toUInt64 <$> read_u8
-- | 0x3b => Ipld.number <$> UInt8.toUInt64 <$> read_u8
-- Major type 4: array
| 0x9f => Ipld.array <$> Array.mk <$> repeat_il deserialize_ipld
-- StringMap
-- Major type 5: map of pairs
| 0xbf => do
  let list ← repeat_il ((·,·) <$> decode_string <*> deserialize_ipld)
  return Ipld.mkObject list
-- Major type 6: tag
| 0xd8 => do 
  let tag ← read_u8
  if tag == 42 then Ipld.link <$> read_link
  else throw (DeserializeError.UnknownCborTag tag)
| 0xf4 => return Ipld.bool false
| 0xf5 => return Ipld.bool true
| 0xf6 => return Ipld.null
| 0xf7 => return Ipld.null
| x => do
  -- Major type 0: unsigned integer
  if 0x00 <= x && x <= 0x17 then return (Ipld.number major.toUInt64)
  -- Major type 1: negative integer
  --if 0x20 <= x && x <= 0x37 then return (Ipld.number major.toUInt64)
  -- Major type 2: byte string
  if 0x40 <= x && x <= 0x5b then do
    let len ← read_len (major.toNat - 0x40)
    let bytes ← read_bytes len
    return Ipld.bytes bytes
  -- Major type 3: text string
  if 0x60 <= x && x <= 0x7b then do
    let len ← read_len (major.toNat - 0x60)
    let str ← read_str len
    return Ipld.string str
  -- Major type 4: array
  if 0x80 <= x && x <= 0x9b then do
    let len ← read_len (major.toNat - 0x80)
    let arr ← repeat_for len deserialize_ipld
    return Ipld.array (Array.mk arr)
  -- Major type 5: map
  if 0xa0 <= x && x <= 0xbb then do
    let len ← read_len (major.toNat - 0xa0)
    let list ← repeat_for len ((·,·) <$> decode_string <*> deserialize_ipld)
    return Ipld.mkObject list
  throw (DeserializeError.UnknownCborTag major)

partial def deserialize (x: ByteArray) : Except DeserializeError Ipld :=
  match EStateM.run deserialize_ipld (ByteCursor.mk x 0) with
  | EStateM.Result.ok x _ => Except.ok x
  | EStateM.Result.error e _ => Except.error e

end Yatima.DagCbor
