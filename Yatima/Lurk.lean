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

def serialize : f → ByteArray := toRepr

end Field

abbrev ScalarPtr [Field f] := f × f

def ScalarPtr.serialize {f : Type} [Field f] (ptr : ScalarPtr f) : Option Cid := 
  let codec := toMultiCodec ptr.1 
  let digest := toMultiHash ptr.2
  match codec with
    | none => none
    | some codec => some ⟨1, codec.toNat, digest⟩

-- TODO : Not sure this is right, but using the lexicographic order on pairs
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

-- TODO : Not sure this is right, but using the lexicographic order on pairs
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

-- TODO: Fix this using the Repr serialization from `store.rs`
inductive Op1 | car | cdr | atom | emit
deriving Repr, BEq, Hashable

def Op1.serialize : Op1 → Ipld
  | car  => .number 0b0010000000000000
  | cdr  => .number 0b0010000000000001
  | atom => .number 0b0010000000000010
  | emit => .number 0b0010000000000011

-- TODO: Fix this using the Repr serialization from `store.rs`
inductive Op2 | sum | diff | prod | quot | cons | begin
deriving Repr, BEq, Hashable

def Op2.serialize : Op2 → Ipld
  | sum   => .number 0b0011000000000000
  | diff  => .number 0b0011000000000001
  | prod  => .number 0b0011000000000010
  | quot  => .number 0b0011000000000011
  | cons  => .number 0b0011000000000100
  | begin => .number 0b0011000000000101

-- TODO: Fix this using the Repr serialization from `store.rs`
inductive Rel2 | eq | nEq
deriving Repr, BEq, Hashable

def Rel2.serialize : Rel2 → Ipld
  | eq  => .number 0b0100000000000000
  | nEq => .number 0b0100000000000001

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

def getCids {f} [Field f] (ptrs : Array (ScalarPtr f)) (cont : ScalarContPtr f) : Option ((Array Cid) × Cid) :=
  let contCid? := cont.serialize
  let ptrCids? := ptrs.sequenceMap (ScalarPtr.serialize) 
  match ptrCids?, contCid? with
    | some cs, some c => some (cs, c)
    | _, _            => none

private def mkSerdeStructure (contName : String) 
                             (ptrNames : Array String)
                             (ptrs : Array Ipld)
                             (cont : Cid) 
                             (op1? : Option Op1)
                             (op2? : Option Op2)
                             (rel2? : Option Rel2) : Ipld :=
  let kvs := ptrNames.zip ptrs
  let kvs := kvs.push ("continuation", .link cont)
  let kvs := match op1? with
    | none => kvs
    | some op1 => kvs.push ("operator", op1.serialize)
  let kvs := match op2? with
    | none => kvs
    | some op2 => kvs.push ("operator", op2.serialize)
  let kvs := match rel2? with
    | none => kvs
    | some rel2 => kvs.push ("operator", rel2.serialize)
  .mkObject [(contName, .mkObject kvs.toList)]

private def ipldStructure (cids? : Option (Array Cid × Cid))
                          (contName : String)
                          (ptrNames : Array String)
                          (op1? : Option Op1 := none)
                          (op2? : Option Op2 := none)
                          (rel2? : Option Rel2 := none) : Ipld :=
  match cids? with
    | none => .null
    | some (cs, c) => 
      let is : Array Ipld := cs.map .link
      mkSerdeStructure contName ptrNames is c op1? op2? rel2?

def serialize (f : Type) [Field f] : ScalarCont f → Ipld
  | outermost => .string "Outermost"
  | error     => .string "Error"
  | dummy     => .string "Dummy"
  | terminal  => .string "Terminal"
  | call ptr1 ptr2 cont => 
    let cids? := getCids #[ptr1, ptr2] cont
    ipldStructure cids? "Call" #["unevaled_arg", "saved_env"]
  | call2 ptr1 ptr2 cont =>
    let cids? := getCids #[ptr1, ptr2] cont
    ipldStructure cids? "Call2" #["unevaled_arg", "saved_env"] 
  | tail ptr1 cont =>
    let cids? := getCids #[ptr1] cont
    ipldStructure cids? "Tail" #["saved_env"]
  | lookup ptr1 cont =>
    let cids? := getCids #[ptr1] cont
    ipldStructure cids? "Lookup" #["saved_env"]
  | unOp op1 cont => 
    match cont.serialize with 
      | none => Ipld.null
      | some c =>  let o := .mkObject [("operator", op1.serialize), ("continuation", .link c)]
         .mkObject [("Unop", o)]
  | binOp op2 ptr1 ptr2 cont =>
    let cids? := getCids #[ptr1, ptr2] cont
    ipldStructure cids? "Binop" #["saved_env", "unevaled_args"] (op2? := some op2)
  | binOp2 op2 ptr1 cont =>
    let cids? := getCids #[ptr1] cont
    ipldStructure cids? "Binop2" #["evaled_arg"] (op2? := some op2)
  | relOp rel2 ptr1 ptr2 cont =>
    let cids? := getCids #[ptr1, ptr2] cont
    ipldStructure cids? "Relop" #["saved_env", "unevaled_args"] (rel2? := some rel2)
  | relOp2 rel2 ptr1 cont =>
    let cids? := getCids #[ptr1] cont
    ipldStructure cids? "Relop2" #["evaled_arg"] (rel2? := some rel2)
  | ifE ptr1 cont =>
    let cids? := getCids #[ptr1] cont
    ipldStructure cids? "If" #["unevaled_args"]
  | letE ptr1 ptr2 ptr3 cont =>
    let cids? := getCids #[ptr1, ptr2, ptr3] cont
    ipldStructure cids? "Let" #["var", "body", "saved_env"]
  | letRec ptr1 ptr2 ptr3 cont =>
    let cids? := getCids #[ptr1, ptr2, ptr3] cont
    ipldStructure cids? "LetRec" #["var", "body", "saved_env"]
  | emit cont => 
    match cont.serialize with
      | none => .null
      | some c => .mkObject [("Emit", .link c)]

end ScalarCont

structure ScalarThunk [Field f] where
  value : ScalarPtr f
  cont  : ScalarContPtr f

namespace ScalarThunk

def serialize {f} [Field f] (thunk : ScalarThunk f) : Ipld := 
  match thunk.value.serialize, thunk.cont.serialize with
    | some cid1, some cid2 => 
      let kvs : Ipld := .mkObject [("value", .link cid1), ("continuation", .link cid2)]
      .mkObject [("ScalarThunk", kvs)]
    | _, _ => Ipld.null

end ScalarThunk

inductive ScalarExpr (f : Type) [Field f]
  | nil   : ScalarExpr  f
  | cons  : ScalarPtr f → ScalarPtr f → ScalarExpr f
  | sym   : String → ScalarExpr f
  -- lam <arg> <body> <closed_env>
  | lam   : ScalarPtr f → ScalarPtr f → ScalarPtr f → ScalarExpr f
  | num   : f → ScalarExpr f
  | str   : String → ScalarExpr f
  | thunk : ScalarThunk f → ScalarExpr f
  | char  : Char → ScalarExpr f

namespace ScalarExpr

def serialize {f} [Field f] : ScalarExpr f → Ipld
  | nil => .string "Nil"
  | cons ptr1 ptr2 => 
    match ptr1.serialize, ptr2.serialize with
      | some cid1, some cid2 => 
        .mkObject [("Cons", .array #[.link cid1, .link cid2])]
      | _, _ => .null
  | sym s => .mkObject [("Sym", .string s)]
  | lam ptr1 ptr2 ptr3 =>
    match ptr1.serialize, ptr2.serialize, ptr3.serialize with
      | some cid1, some cid2, some cid3 =>
        let kvs := .mkObject [("arg", .link cid1), ("body", .link cid2), ("closed_env", .link cid3)]
        .mkObject [("Fun", kvs)]
      | _, _, _ => .null
  | num a => 
    let bs : ByteArray := Field.serialize a 
    .mkObject [("Num", .bytes bs)]
  | str s => .mkObject [("Str", .string s)]
  | thunk sth => .mkObject [("Thunk", sth.serialize)]
  | char c => .mkObject [("Char", .string s!"{c}")]

end ScalarExpr

instance [Field f] : Inhabited $ ScalarExpr f where
  default := .nil

open Std in
structure ScalarStore [Field f] where
  scalarMap : RBMap (ScalarPtr f) (Option $ ScalarExpr f) compare
  scalarContMap : RBMap (ScalarContPtr f) (Option $ ScalarCont f) compare

namespace ScalarStore

-- def serialize {f} [Field f] (store : ScalarStore f) : Ipld := 
--   let scMapList := store.scalarMap.toList
--   let scContMapList := store.scalarMap.toList

end ScalarStore

end Lurk
