import Std.Data.RBMap

namespace Prime

class Field (f : Type) where
  toRepr : f → UInt64

instance (f : Type) [Field f] : Ord f where
  compare a b := compare (Field.toRepr a) (Field.toRepr b)

end Prime
namespace Lurk

class Field (f : Type) [Prime.Field f] where
  fieldCodec : UInt64
  hashCodec : UInt64
  lurkCodecPrefix : UInt64 := 0xc0de
  numBytes : USize
deriving Repr, BEq, Ord

variable (f : Type) [Prime.Field f]

abbrev ScalarPtr [Field f] := f × f

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

inductive Op1 | car | cdr | atom | emit
deriving Repr, BEq, Hashable

inductive Op2 | sum | diff | prod | quot | cons | begin
deriving Repr, BEq, Hashable

inductive Rel2 | eq | nEq
deriving Repr, BEq, Hashable

inductive ScalarCont (f : Type) [Prime.Field f] [Field f] 
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

structure ScalarThunk [Field f] where
  value : ScalarPtr f
  cont  : ScalarContPtr f

inductive ScalarExpr (f : Type) [Prime.Field f] [Field f]
  | nil   : ScalarExpr  f
  | cons  : ScalarPtr f → ScalarPtr f → ScalarExpr f
  | sym   : String → ScalarExpr f
  -- lam <arg> <body> <closed_env>
  | lam   : ScalarPtr f → ScalarPtr f → ScalarPtr f → ScalarExpr f
  | num   : f → ScalarExpr f
  | str   : String → ScalarExpr f
  | thunk : ScalarThunk f → ScalarExpr f

instance [Field f] : Inhabited $ ScalarExpr f where
  default := .nil

-- TODO : Should be a better way of extracting the ordering without using `@`
open Std in
structure ScalarStore [Field f] where
  scalarMap : RBMap (ScalarPtr f) (Option $ ScalarExpr f) (@compare (ScalarPtr f) _) 
  scalarContMap : RBMap (ScalarContPtr f) (Option $ ScalarCont f) (@compare (ScalarContPtr f) _)
  pendingScalarPtrs : List (ScalarPtr f)

end Lurk
