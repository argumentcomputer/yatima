/-
The serialization comes an attempt to translate between the `Lurk` types and `Ipld`. 

The translation comes as a composition of taking `Lurk` types (as defined in this file) to the `Serde` 
[data model](https://serde.rs/data-model.html), and followed by a translation of the `Serde` to `Ipld` 
[data model](https://ipld.io/docs/data-model/). 

`Lurk` types to `serde` largely determined via metaprogramming using `derive`d attributes. These are
all read off from <https://github.com/lurk-lang/lurk-rs/> 

`Serde` to `Ipld` may be interpreted via the <https://github.com/ipld/libipld/blob/master/core/src/serde/ser.rs>
description. Though in this file we use the scheme proposed in the following PR for `libipld`
<https://github.com/ipld/libipld/pull/147>
-/
import Std.Data.RBMap
import Ipld.Utils
import Ipld.Cid
import Ipld.Multihash
import Ipld.Ipld


/-- Not exactly
https://github.com/multiformats/rust-multihash/blob/3a3dacf470dca2110e8ec111f5322ebb2c38bbb0/src/multihash.rs#L99

because our Ipld multihash implementation is not strict about multihash size
-/
def wrap (code : UInt64) (digest : ByteArray) : Multihash := ⟨code.toNat, digest.size, digest⟩

namespace Lurk

/--
This is an amalgam of 
https://github.com/lurk-lang/lurk-rs/blob/f779b840c774056b8b7361eee8922046f16fcd07/src/field.rs#L8
and
https://github.com/zkcrypto/ff/blob/9b9a8d9c363ecbf7bb4c79998aaed32c1f8ce027/src/lib.rs#L130

I believe `toTag`/`fromTag` are derivable from `toRepr`/`fromRepr` (and vice versa)?
-/
class Field (f : Type) where
  fromRepr : ByteArray → f
  toRepr   : f → ByteArray
  fieldCodec : UInt64
  hashCodec : UInt64
  lurkCodecPrefix : UInt64 := 0xc0de
  numBytes : USize
  toTag : f → Option UInt32
  fromTag : UInt32 → f

open Field

variable (f : Type) [Field f]

instance : Ord f where
  compare a b := compare (toRepr a) (toRepr b)

instance : BEq f where
  beq a b := (toRepr a) == (toRepr b)

instance : ToString f where
  toString a := toString (toRepr a)

namespace Field

variable {f : Type} [Field f]

/-- Implementation from
https://github.com/lurk-lang/lurk-rs/blob/be7e18f8e73bcd81ee0e63441fe3c023ffd94e2d/src/field.rs#L27
-/
def toMultiCodec (x: f) : Option UInt64 := match toTag x with
  | some tag => 
    some $ (lurkCodecPrefix f) <<< 48 ||| (fieldCodec f) <<< 32 ||| tag.toUInt64  
  | none     => none

/-- Implementation from
https://github.com/lurk-lang/lurk-rs/blob/be7e18f8e73bcd81ee0e63441fe3c023ffd94e2d/src/field.rs#L44
-/
def toMultiHash (x : f) : Multihash := wrap (hashCodec f) (toRepr x)

/--
https://github.com/lurk-lang/lurk-rs/blob/f779b840c774056b8b7361eee8922046f16fcd07/src/field.rs#L129
Lurk field serialization is treated in terms of ByteArrays
-/
def serialize : f → ByteArray := toRepr

end Field

abbrev ScalarPtr [Field f] := f × f

def ScalarPtr.serialize {f : Type} [Field f] (ptr : ScalarPtr f) : Option Cid := 
  let codec := toMultiCodec ptr.1 
  let digest := toMultiHash ptr.2
  match codec with
    | none => none
    | some codec => some ⟨1, codec.toNat, digest⟩

-- Not sure this is right, but using the lexicographic order on pairs
-- <https://github.com/lurk-lang/lurk-rs/blob/0f9a0b3ab0c04e0b4aa34414c10f4495c6e47755/src/store.rs#L232>
instance [Field f] : Ord (ScalarPtr f) where
  compare ptr1 ptr2 := match ptr1, ptr2 with
    | (a, b) , (c, d) => match compare a c with
      | .gt => .gt
      | .lt => .lt
      | .eq => match compare b d with
        | .gt => .gt
        | .lt => .lt
        | .eq => .eq

abbrev ScalarContPtr [Field f] := f × f

def ScalarContPtr.serialize {f : Type} [Field f] (ptr : ScalarContPtr f) : Option Cid := 
  let codec := toMultiCodec ptr.1 
  let digest := toMultiHash ptr.2
  match codec with
    | none => none
    | some codec => some ⟨1, codec.toNat, digest⟩

-- Not sure this is right, but using the lexicographic order on pairs
-- <https://github.com/lurk-lang/lurk-rs/blob/0f9a0b3ab0c04e0b4aa34414c10f4495c6e47755/src/store.rs#L315>
instance [Field f] : Ord (ScalarContPtr f) where
  compare ptr1 ptr2 := match ptr1, ptr2 with
    | (a, b) , (c,d ) => match compare a c with
      | .gt => .gt
      | .lt => .lt
      | .eq => match compare b d with
        | .gt => .gt
        | .lt => .lt
        | .eq => .eq

inductive Op1 | car | cdr | atom | emit
deriving Repr, BEq, Hashable

-- The serialization is derived by the representation taken from the `serialize_repr` derive method and
-- <https://github.com/lurk-lang/lurk-rs/blob/f779b840c774056b8b7361eee8922046f16fcd07/src/store.rs#L435>
def Op1.serialize : Op1 → Ipld
  | car  => .number 0b0010000000000000
  | cdr  => .number 0b0010000000000001
  | atom => .number 0b0010000000000010
  | emit => .number 0b0010000000000011

-- Same as above
inductive Op2 | sum | diff | prod | quot | cons | begin
deriving Repr, BEq, Hashable

def Op2.serialize : Op2 → Ipld
  | sum   => .number 0b0011000000000000
  | diff  => .number 0b0011000000000001
  | prod  => .number 0b0011000000000010
  | quot  => .number 0b0011000000000011
  | cons  => .number 0b0011000000000100
  | begin => .number 0b0011000000000101

-- Same as above
inductive Rel2 | eq | nEq
deriving Repr, BEq, Hashable

def Rel2.serialize : Rel2 → Ipld
  | eq  => .number 0b0100000000000000
  | nEq => .number 0b0100000000000001


/--
The definition and serialization of continuations is determined from the `Serialize` derived attribute of 
<https://github.com/lurk-lang/lurk-rs/blob/f779b840c774056b8b7361eee8922046f16fcd07/src/scalar_store.rs#L232>
wherein each enum is a struct variant. 
-/
inductive ScalarCont (f : Type) [Field f] 
  | outermost
  -- call <unevaled_arg> <saved_env> <continuation>
  | call : ScalarPtr f → ScalarPtr f → ScalarContPtr f → ScalarCont f
  -- call2 <function> <saved_env> <continuation>
  | call2 : ScalarPtr f → ScalarPtr f → ScalarContPtr f → ScalarCont f
  -- tail <saved_env> <continuation>
  | tail : ScalarPtr f → ScalarContPtr f → ScalarCont f
  | error
  -- lookup <saved_env> <continuation>
  | lookup : ScalarPtr f → ScalarContPtr f → ScalarCont f
  -- unOp <operator> <continuation>
  | unOp : Op1 → ScalarContPtr f → ScalarCont f
  -- binOp <operator> <saved_env> <unevaled_args> <continuation>
  | binOp : Op2 → ScalarPtr f → ScalarPtr f → ScalarContPtr f → ScalarCont f
  -- binOp2 <operator> <evaled_arg> <continuation>
  | binOp2 : Op2 → ScalarPtr f → ScalarContPtr f → ScalarCont f
  -- relOp <operator> <saved_env> <unevaled_args> <continuation> 
  | relOp : Rel2 → ScalarPtr f → ScalarPtr f → ScalarContPtr f → ScalarCont f
  -- relOp2 <operator> <evaled_arg> <continuation>
  | relOp2 : Rel2 → ScalarPtr f → ScalarContPtr f → ScalarCont f
  -- ifE <unevaled_args> <continuation>
  | ifE : ScalarPtr f → ScalarContPtr f → ScalarCont f
  -- letE <var> <body> <saved_env> <continuation>
  | letE : ScalarPtr f → ScalarPtr f → ScalarPtr f → ScalarContPtr f → ScalarCont f
  -- letRec <var> <body> <saved_env> <continuation>
  | letRec : ScalarPtr f → ScalarPtr f → ScalarPtr f → ScalarContPtr f → ScalarCont f
  -- emit <continuation>
  | emit : ScalarContPtr f → ScalarCont f
  | dummy
  | terminal

namespace ScalarCont

private def getCids {f} [Field f] (ptrs : Array (ScalarPtr f)) (cont : ScalarContPtr f) : Option (Array Cid) :=
  let contCid? := cont.serialize
  let ptrCids? := ptrs.sequenceMap (ScalarPtr.serialize) 
  match ptrCids?, contCid? with
    | some cs, some c => some $ cs.push c
    | _, _            => none

private def serializeCids (cids? : Option $ Array Cid)
                          (op1? : Option $ Op1 := none)
                          (op2? : Option $ Op2 := none)
                          (rel2? : Option $ Rel2 := none) : Ipld := match cids? with
  | some cids => 
    let op := match op1?, op2?, rel2? with
      | some op1, _, _ => op1.serialize
      | _, some op2, _ => op2.serialize
      | _, _ , some rel2 => rel2.serialize
      | _, _, _ => Ipld.null
  .array <| cids.map .link ++ #[op]
  | none => Ipld.null

def serialize (f : Type) [Field f] : ScalarCont f → Ipld
  | outermost => .array #[.number 0]
  | call ptr1 ptr2 cont => 
    let cids? := getCids #[ptr1, ptr2] cont
    .array #[.number 1, serializeCids cids?]
  | call2 ptr1 ptr2 cont =>
    let cids? := getCids #[ptr1, ptr2] cont
    .array #[.number 2, serializeCids cids?]
  | tail ptr1 cont =>
    let cids? := getCids #[ptr1] cont
    .array #[.number 3, serializeCids cids?]
  | error     => .array #[.number 4]
  | lookup ptr1 cont =>
    let cids? := getCids #[ptr1] cont
    .array #[.number 5, serializeCids cids?]
  | unOp op1 cont => 
    match cont.serialize with 
      | none => Ipld.null
      | some c =>  let o := .array #[op1.serialize , .link c]
         .array #[.number 6, o]
  | binOp op2 ptr1 ptr2 cont =>
    let cids? := getCids #[ptr1, ptr2] cont
    .array #[.number 7, serializeCids cids? (op2? := some op2)]
  | binOp2 op2 ptr1 cont =>
    let cids? := getCids #[ptr1] cont
    .array #[.number 8, serializeCids cids? (op2? := some op2)]
  | relOp rel2 ptr1 ptr2 cont =>
    let cids? := getCids #[ptr1, ptr2] cont
    .array #[.number 9, serializeCids cids? (rel2? := some rel2)]
  | relOp2 rel2 ptr1 cont =>
    let cids? := getCids #[ptr1] cont
    .array #[.number 10, serializeCids cids? (rel2? := some rel2)]
  | ifE ptr1 cont =>
    let cids? := getCids #[ptr1] cont
    .array #[.number 11, serializeCids cids?]
  | letE ptr1 ptr2 ptr3 cont =>
    let cids? := getCids #[ptr1, ptr2, ptr3] cont
    .array #[.number 12, serializeCids cids?]
  | letRec ptr1 ptr2 ptr3 cont =>
    let cids? := getCids #[ptr1, ptr2, ptr3] cont
    .array #[.number 13, serializeCids cids?]
  | emit cont => 
    match cont.serialize with
      | none => .null
      | some c => .array #[.number 14, .array #[.link c]]
  | dummy     => .array #[.number 15]
  | terminal  => .array #[.number 16]

end ScalarCont

/--
Definition and serialization taken from.
https://github.com/lurk-lang/lurk-rs/blob/f779b840c774056b8b7361eee8922046f16fcd07/src/scalar_store.rs#L223
-/
structure ScalarThunk [Field f] where
  value : ScalarPtr f
  cont  : ScalarContPtr f

namespace ScalarThunk

def serialize {f} [Field f] (thunk : ScalarThunk f) : Ipld := 
  match thunk.value.serialize, thunk.cont.serialize with
    | some cid1, some cid2 => 
      .array $ #[cid1, cid2].map .link
    | _, _ => Ipld.null

end ScalarThunk

/--
Definition and serialization are taken from
https://github.com/lurk-lang/lurk-rs/blob/f779b840c774056b8b7361eee8922046f16fcd07/src/scalar_store.rs#L153
wherein `nil` is a unit-type enum variant, `cons`, `comm` are tuple variants, `sym`, `num`, `str`,
`thunk`, and `char` are `lam` is a struct variant
-/
inductive ScalarExpr (f : Type) [Field f]
  | nil   : ScalarExpr  f
  | cons  : ScalarPtr f → ScalarPtr f → ScalarExpr f
  | comm : f → ScalarPtr f → ScalarExpr f
  | sym   : String → ScalarExpr f
  -- lam <arg> <body> <closed_env>
  | lam   : ScalarPtr f → ScalarPtr f → ScalarPtr f → ScalarExpr f
  | num   : f → ScalarExpr f
  | str   : String → ScalarExpr f
  | thunk : ScalarThunk f → ScalarExpr f
  | char  : Char → ScalarExpr f

namespace ScalarExpr

def serialize {f} [Field f] : ScalarExpr f → Ipld
  | nil => .array #[.number 0]
  | cons ptr1 ptr2 => 
    match ptr1.serialize, ptr2.serialize with
      | some cid1, some cid2 => 
        .array #[.number 1, .array $ #[cid1, cid2].map .link]
      | _, _ => .null
  | comm a ptr => 
    let bs : ByteArray := Field.serialize a
    match ptr.serialize with
      | some cid => 
        .array #[.number 2, .array $ #[.bytes bs, .link cid]]
      | none => Ipld.null
  | sym s => .array #[.number 3, .string s]
  | lam ptr1 ptr2 ptr3 =>
    match ptr1.serialize, ptr2.serialize, ptr3.serialize with
      | some cid1, some cid2, some cid3 =>
        .array #[.number 4, .array $ #[cid1, cid2, cid3].map .link]
      | _, _, _ => .null
  | num a => 
    let bs : ByteArray := Field.serialize a 
    .array #[.number 5, .bytes bs]
  | str s => .array #[.number 6, .string s]
  | thunk sth => .array #[.number 7, sth.serialize]
  | char c => .array #[.number 8, .string s!"{c}"]

end ScalarExpr

instance [Field f] : Inhabited $ ScalarExpr f where
  default := .nil

open Std

/--
Definition and serialization are taken from. 
https://github.com/lurk-lang/lurk-rs/blob/f779b840c774056b8b7361eee8922046f16fcd07/src/scalar_store.rs#L12
It should be noted that the serialization used here allows for keys that are not `String`s because of
<https://github.com/ipld/libipld/pull/147>
-/
structure ScalarStore [Field f] where
  scalarMap : RBMap (ScalarPtr f) (Option $ ScalarExpr f) compare
  scalarContMap : RBMap (ScalarContPtr f) (Option $ ScalarCont f) compare

namespace ScalarStore

private def serExprAux {α} {f} [Field f] (ser : α → Option Cid) (p : α × Option (ScalarExpr f)) : Ipld := 
  match ser p.fst, p.snd with
    | some cid, some exp => .array #[.link cid, exp.serialize]
    | _, _ => .null

private def serContAux {α} {f} [Field f] (ser : α → Option Cid) (p : α × Option (ScalarCont f)) : Ipld := .null

def serialize {f} [Field f] (store : ScalarStore f) : Ipld := 
  let scMapList := store.scalarMap.toList
  let ptrIpldList : List Ipld := scMapList.map (serExprAux (ScalarPtr.serialize))
  let scContMapList := store.scalarContMap.toList
  let contIpldList : List Ipld := scContMapList.map (serContAux (ScalarContPtr.serialize))
  .array #[.array ptrIpldList.toArray, .array contIpldList.toArray]

end ScalarStore

end Lurk
