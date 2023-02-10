import Lurk.Field
import Poseidon.ForLurk
import Std.Data.RBMap

namespace Lurk

/-! placeholder types -/

inductive LDON
  | num : F → LDON
  | str : String → LDON
  | sym : String → LDON
  | cons : LDON → LDON → LDON
  deriving Inhabited, Ord

inductive Tag
  | nil | cons | sym | num | str | char | comm
  deriving Ord

def Tag.toF : Tag → F
  | .nil   => .ofNat 0
  | .cons  => .ofNat 1
  | .sym   => .ofNat 2
  | .num   => .ofNat 3
  | .str   => .ofNat 4
  | .char  => .ofNat 5
  | .comm  => .ofNat 6

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Ord

inductive ScalarExpr
  | cons (car : ScalarPtr) (cdr : ScalarPtr)
  | comm (x : F) (ptr : ScalarPtr)
  | sym (sym : ScalarPtr)
  | num (val : F)
  | strCons (head : ScalarPtr) (tail : ScalarPtr)
  | strNil
  | char (x : F)

open Std (RBMap)
structure LDONHashState where
  exprs      : RBMap ScalarPtr   (Option ScalarExpr) compare
  comms      : RBMap F           ScalarPtr           compare
  charsCache : RBMap (List Char) ScalarPtr           compare
  ldonCache  : RBMap LDON        ScalarPtr           compare
  deriving Inhabited

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofNat $ (Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val).norm

abbrev HashM := StateM LDONHashState

def addExprHash (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr (some expr) })

def addCommitment (hash : F) (ptr : ScalarPtr) : HashM F :=
  modifyGet fun stt => (hash, { stt with comms := stt.comms.insert hash ptr })

def hashChars (s : List Char) : HashM ScalarPtr := do
  match (← get).charsCache.find? s with
  | some ptr => pure ptr
  | none =>
    let ptr ← match s with
      | [] => addExprHash ⟨.str, F.zero⟩ .strNil
      | c :: cs =>
        let n := .ofNat c.toNat
        let headPtr ← addExprHash ⟨.char, n⟩ (.char n)
        let tailPtr ← hashChars cs
        addExprHash ⟨.str, hashPtrPair headPtr tailPtr⟩ (.strCons headPtr tailPtr)
    modifyGet fun stt =>
      (ptr, { stt with charsCache := stt.charsCache.insert s ptr })

def hashLDON (x : LDON) : HashM ScalarPtr := do
  match (← get).ldonCache.find? x with
  | some ptr => pure ptr
  | none =>
    let ptr ← match x with
      | .sym "NIL" =>
        let ptr := ⟨.nil, .ofNat 0⟩
        addExprHash ptr (.sym ptr)
      | .num n => let n := .ofNat n; addExprHash ⟨.num, n⟩ (.num n)
      | .str s => hashChars s.data
      | .sym s =>
        let ptr ← hashChars s.data
        addExprHash ⟨.sym, ptr.val⟩ (.sym ptr)
      | .cons car cdr =>
        let car ← hashLDON car
        let cdr ← hashLDON cdr
        addExprHash ⟨.cons, hashPtrPair car cdr⟩ (.cons car cdr)
    modifyGet fun stt =>
      (ptr, { stt with ldonCache := stt.ldonCache.insert x ptr })

def hideLDON (secret : F) (x : LDON) : HashM F := do
  let ptr ← hashLDON x
  addCommitment (hashPtrPair ⟨.comm, secret⟩ ptr ) ptr

def LDON.commit (ldon : LDON) (stt : LDONHashState) : F × LDONHashState :=
  StateT.run (hideLDON (.ofNat 0) ldon) stt

end Lurk
