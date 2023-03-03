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
  deriving Ord, Repr

def Tag.toF : Tag → F
  | .nil  => .ofNat 0
  | .cons => .ofNat 1
  | .sym  => .ofNat 2
  | .num  => .ofNat 3
  | .str  => .ofNat 4
  | .char => .ofNat 5
  | .comm => .ofNat 6

def Tag.ofF : F → Option Tag
  | .ofNat 0 => return .nil
  | .ofNat 1 => return .cons
  | .ofNat 2 => return .sym
  | .ofNat 3 => return .num
  | .ofNat 4 => return .str
  | .ofNat 5 => return .char
  | .ofNat 6 => return .comm
  | _ => none

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Ord, Repr

inductive ScalarExpr
  | cons (car : ScalarPtr) (cdr : ScalarPtr)
  | comm (x : F) (ptr : ScalarPtr)
  | sym (sym : ScalarPtr)
  | num (val : F)
  | strCons (head : ScalarPtr) (tail : ScalarPtr)
  | strNil
  | char (x : F)

open Std (RBMap RBSet)
structure LDONHashState where
  exprs      : RBMap ScalarPtr   ScalarExpr compare
  comms      : RBMap F           ScalarPtr  compare
  charsCache : RBMap (List Char) ScalarPtr  compare
  ldonCache  : RBMap LDON        ScalarPtr  compare
  deriving Inhabited

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofNat $ (Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val).norm

abbrev HashM := StateM LDONHashState

def addExprHash (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr expr })

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
        -- `nil` has its own tag instead of `.sym`. Thus we need to manually
        -- hash it as a string and make a `.nil` pointer with it
        let ptr ← hashChars ['N', 'I', 'L']
        addExprHash ⟨.nil, ptr.val⟩ (.sym ptr)
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

structure Store where
  exprs : RBMap ScalarPtr ScalarExpr compare
  comms : RBMap F         ScalarPtr  compare
  deriving Inhabited

partial def loadExprs (ptr : ScalarPtr) (seen : RBSet ScalarPtr compare)
  (src acc : RBMap ScalarPtr ScalarExpr compare) :
    RBMap ScalarPtr ScalarExpr compare × RBSet ScalarPtr compare :=
  if seen.contains ptr then (acc, seen) else
    let seen := seen.insert ptr
    match src.find? ptr with
    | none => panic! s!"{repr ptr} not found in store"
    | some expr => match expr with
      | .cons x y | .strCons x y =>
        let (acc, seen) := loadExprs x seen src (acc.insert ptr expr)
        loadExprs y seen src acc
      | .comm _ x | .sym x => loadExprs x seen src (acc.insert ptr expr)
      | _ => (acc, seen)

def LDONHashState.storeFromCommits
    (stt : LDONHashState) (comms : Array Lurk.F) : Store :=
  let (exprs, comms, _) := comms.foldl (init := default)
    fun (exprsAcc, (commsAcc : RBMap F ScalarPtr compare), seen) f =>
      match stt.comms.find? f with
      | none => panic! s!"{f} not found in store"
      | some ptr =>
        let (exprsAcc, seen) := loadExprs ptr seen stt.exprs exprsAcc
        (exprsAcc, commsAcc.insert f ptr, seen)
  ⟨exprs, comms⟩

end Lurk
