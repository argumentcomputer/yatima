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
  .ofNat $ (Poseidon.Lurk.hash4 x.tag.toF x.val y.tag.toF y.val).norm

def hashFPtr (f : F) (x : ScalarPtr) : F :=
  .ofNat $ (Poseidon.Lurk.hash3 f x.tag.toF x.val).norm

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
  addCommitment (hashFPtr secret ptr) ptr

def LDON.commit (ldon : LDON) (stt : LDONHashState) : F × LDONHashState :=
  StateT.run (hideLDON (.ofNat 0) ldon) stt

#eval (LDON.sym "NIL").commit default |>.1.asHex
-- expected: 0x3fddeb1275663f07154d612a0c2e8271644e9ed24a15bbf6864f51f63dbf5b88

#eval (LDON.num (.ofNat 0)).commit default |>.1.asHex
-- expected: 0x0fa797fb1ca00c0148d4dd316cb38aad581e07bb70b058043ef6e4083fbea38c

#eval (LDON.num (.ofNat 123)).commit default |>.1.asHex
-- expected: 0x2937881eff06c2bcc2c8c1fa0818ae3733c759376f76fc10b7439269e9aaa9bc

#eval (LDON.str "hi").commit default |>.1.asHex
-- expected: 0x0e8d1757f0667044887a7824bb20918921a45294146c3d5fddddff06fd595ac8

#eval (LDON.sym "HI").commit default |>.1.asHex
-- expected: 0x0eff8a974e0c469e77fc97684fea73cc7936fa0fe75c3430426746c22395f2f2

#eval (LDON.cons (.str "hi") (.str "bye")).commit default |>.1.asHex
-- expected: 0x1113dac6b0057dcf0c9d73cc4e38aab94565175592d67aecea09d60a3345d7e9

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
