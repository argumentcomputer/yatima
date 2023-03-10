import Lurk.Field
import Poseidon.ForLurk
import Std.Data.RBMap

namespace Lurk

/-! placeholder types -/

inductive LDON
  | nil
  | num : F → LDON
  | str : String → LDON
  | cons : LDON → LDON → LDON
  deriving Inhabited, Ord

inductive Tag
  | nil | cons | sym | num | str | char | comm
  deriving Ord, Repr

def Tag.toF : Tag → F
  | .nil   => .ofNat 0
  | .cons  => .ofNat 1
  | .sym   => .ofNat 2
  | .num   => .ofNat 4
  | .str   => .ofNat 6
  | .char  => .ofNat 7
  | .comm  => .ofNat 8

def Tag.ofF : F → Option Tag
  | .ofNat 0 => return .nil
  | .ofNat 1 => return .cons
  | .ofNat 2 => return .sym
  | .ofNat 4 => return .num
  | .ofNat 6 => return .str
  | .ofNat 7 => return .char
  | .ofNat 8 => return .comm
  | _ => none

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Ord, Repr

inductive ScalarExpr
  | cons : ScalarPtr → ScalarPtr → ScalarExpr
  | strCons : ScalarPtr → ScalarPtr → ScalarExpr
  | symCons : ScalarPtr → ScalarPtr → ScalarExpr
  | comm : F → ScalarPtr → ScalarExpr
  | num : F → ScalarExpr
  | char : F → ScalarExpr
  | nil
  | strNil
  | symNil
  deriving Repr

open Std (RBMap RBSet)
structure LDONHashState where
  exprs      : RBMap ScalarPtr   (Option ScalarExpr) compare
  charsCache : RBMap (List Char) ScalarPtr           compare
  ldonCache  : RBMap LDON        ScalarPtr           compare
  deriving Inhabited

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofNat $ (Poseidon.Lurk.hash4 x.tag.toF x.val y.tag.toF y.val).norm

def hashFPtr (f : F) (x : ScalarPtr) : F :=
  .ofNat $ (Poseidon.Lurk.hash3 f x.tag.toF x.val).norm

abbrev HashM := StateM LDONHashState

def addExprHash (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr (some expr) })

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
      | .nil =>
        let rootPtr ← addExprHash ⟨.sym, F.zero⟩ .symNil
        let nilPtr  ← hashChars ['N', 'I', 'L']
        let lurkPtr ← hashChars ['L', 'U', 'R', 'K']
        let symPtr1 ← addExprHash ⟨.sym, hashPtrPair lurkPtr rootPtr⟩ (.symCons lurkPtr rootPtr)
        addExprHash ⟨.nil, hashPtrPair nilPtr symPtr1⟩ (.symCons nilPtr symPtr1)
      | .num n => let n := .ofNat n; addExprHash ⟨.num, n⟩ (.num n)
      | .str s => hashChars s.data
      | .cons car cdr =>
        let car ← hashLDON car
        let cdr ← hashLDON cdr
        addExprHash ⟨.cons, hashPtrPair car cdr⟩ (.cons car cdr)
    modifyGet fun stt =>
      (ptr, { stt with ldonCache := stt.ldonCache.insert x ptr })

def hideLDON (secret : F) (x : LDON) : HashM F := do
  let ptr ← hashLDON x
  let hash := hashFPtr secret ptr
  discard $ addExprHash ⟨.comm, hash⟩ (.comm hash ptr)
  return hash

def LDON.commit (ldon : LDON) (stt : LDONHashState) : F × LDONHashState :=
  StateT.run (hideLDON (.ofNat 0) ldon) stt

abbrev Store := RBMap ScalarPtr (Option ScalarExpr) compare

end Lurk
