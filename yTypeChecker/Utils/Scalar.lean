prelude
import yTypeChecker.Utils.LDON
import yTypeChecker.Utils.Poseidon.ForLurk
import yTypeChecker.Utils.YSL.List

namespace Lurk.Scalar

inductive Tag
  | nil | cons | sym | num | str | char | comm | u64
  deriving Ord, Repr

def Tag.toF : Tag → F
  | .nil  => .ofNat 0
  | .cons => .ofNat 1
  | .sym  => .ofNat 2
  | .num  => .ofNat 4
  | .str  => .ofNat 6
  | .char => .ofNat 7
  | .comm => .ofNat 8
  | .u64  => .ofNat 9

def Tag.ofF : F → Option Tag
  | .ofNat 0 => return .nil
  | .ofNat 1 => return .cons
  | .ofNat 2 => return .sym
  | .ofNat 4 => return .num
  | .ofNat 6 => return .str
  | .ofNat 7 => return .char
  | .ofNat 8 => return .comm
  | .ofNat 9 => return .u64
  | _ => none

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Ord, Repr

@[inline] def ScalarPtr.isImmediate (ptr : ScalarPtr) : Bool :=
  ptr matches ⟨.num, _⟩ | ⟨.u64, _⟩| ⟨.char, _⟩ | ⟨.str, F.zero⟩ | ⟨.sym, F.zero⟩

inductive ScalarExpr
  | cons : ScalarPtr → ScalarPtr → ScalarExpr
  | strCons : ScalarPtr → ScalarPtr → ScalarExpr
  | symCons : ScalarPtr → ScalarPtr → ScalarExpr
  | comm : F → ScalarPtr → ScalarExpr
  | nil
  deriving Repr

open Batteries (RBMap RBSet)

abbrev Store := RBMap ScalarPtr (Option ScalarExpr) compare

structure StoreCtx where
  store   : Store
  visited : RBSet ScalarPtr compare
  deriving Inhabited

abbrev OpenM := ReaderT StoreCtx $ ExceptT String Id

@[inline] def OpenM.withVisited (ptr : ScalarPtr) : OpenM α → OpenM α :=
  withReader fun ctx => { ctx with visited := ctx.visited.insert ptr }

partial def loadLDON (ptr : ScalarPtr) : OpenM LDON := do
  if (← read).visited.contains ptr then throw s!"Cycle detected at {repr ptr}"
  else match ptr with
    | ⟨.nil, _⟩ => return .nil
    | ⟨.str, .zero⟩ => return .str ""
    | ⟨.sym, .zero⟩ => return .sym ""
    | ⟨.char, f⟩ => return .char $ .ofNat f.val
    | ⟨.num, f⟩ => return .num f
    | ⟨.u64, f⟩ => return .u64 $ .ofNat f.val
    | _ => OpenM.withVisited ptr do match (← read).store.find? ptr with
      | none => throw s!"Expression for {repr ptr} not found"
      | some none => throw "Can't open opaque data"
      | some $ some expr => match expr with
        | .cons x y => return .cons (← loadLDON x) (← loadLDON y)
        | .strCons x y => match x, ← loadLDON y with
          | ⟨.char, c⟩, .str cs => return .str ⟨.ofNat c :: cs.data⟩
          | _, _ => throw s!"Malformed expression for a string: {repr expr}"
        | .symCons x _ => match ← loadLDON x with
          | .str x => return .sym x
          | _ => throw s!"Malformed expression for a symbol: {repr expr}"
        | _ => unreachable!

def openCommM (comm : F) : OpenM LDON := do
  match (← read).store.find? ⟨.comm, comm⟩ with
  | none => throw s!"Commitment for {comm.asHex} not found"
  | some $ some (.comm _ ptr) => loadLDON ptr
  | _ => throw "Invalid commitment expression. Malformed store"

def Store.open (store : Store) (comm : F) : Except String LDON :=
  ReaderT.run (openCommM comm) ⟨store, default⟩

structure LDONHashState where
  store      : Store
  charsCache : RBMap (List Char) ScalarPtr compare
  ldonCache  : RBMap LDON        ScalarPtr compare
  deriving Inhabited

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofNat $ (Poseidon.Lurk.hash4 x.tag.toF x.val y.tag.toF y.val).norm

def hashFPtr (f : F) (x : ScalarPtr) : F :=
  .ofNat $ (Poseidon.Lurk.hash3 f x.tag.toF x.val).norm

abbrev HashM := StateM LDONHashState

def addExprHash (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  if ptr.isImmediate then pure ptr
  else modifyGet fun stt =>
    (ptr, { stt with store := stt.store.insert ptr (some expr) })

def hashChars (cs : List Char) : HashM ScalarPtr := do
  match (← get).charsCache.find? cs with
  | some ptr => pure ptr
  | none =>
    let ptr ← match cs with
      | [] => pure ⟨.str, F.zero⟩
      | c :: cs =>
        let headPtr := ⟨.char, .ofNat c.toNat⟩
        let tailPtr ← hashChars cs
        addExprHash ⟨.str, hashPtrPair headPtr tailPtr⟩ (.strCons headPtr tailPtr)
    modifyGet fun stt =>
      (ptr, { stt with charsCache := stt.charsCache.insert cs ptr })

def hashStrings (ss : List String) : HashM ScalarPtr :=
  ss.foldrM (init := ⟨.sym, F.zero⟩) fun s acc => do
    let strPtr ← hashChars s.data
    addExprHash ⟨.sym, hashPtrPair strPtr acc⟩ (.symCons strPtr acc)

def hashLDON (x : LDON) : HashM ScalarPtr := do
  match (← get).ldonCache.find? x with
  | some ptr => pure ptr
  | none =>
    let ptr ← match x with
      | .nil => addExprHash ⟨.nil, (← hashStrings ["NIL", "LURK"]).val⟩ .nil
      | .num n => pure ⟨.num, n⟩
      | .u64 n => pure ⟨.u64, .ofNat n.val⟩
      | .char n => pure ⟨.char, .ofNat n.toNat⟩
      | .str s => hashChars s.data
      | .sym s => hashStrings [s, "LURK"]
      | .cons car cdr =>
        let car ← hashLDON car
        let cdr ← hashLDON cdr
        addExprHash ⟨.cons, hashPtrPair car cdr⟩ (.cons car cdr)
    modifyGet fun stt =>
      (ptr, { stt with ldonCache := stt.ldonCache.insert x ptr })

def hideLDON (secret : F) (x : LDON) : HashM F := do
  let ptr ← hashLDON x
  let hash := hashFPtr secret ptr
  discard $ addExprHash ⟨.comm, hash⟩ (.comm secret ptr)
  return hash

abbrev ExtractM := ReaderT StoreCtx $ ExceptT String $ StateM Store

@[inline] def ExtractM.withVisited (ptr : ScalarPtr) : ExtractM α → ExtractM α :=
  withReader fun ctx => { ctx with visited := ctx.visited.insert ptr }

partial def loadExprs (ptr : ScalarPtr) : ExtractM Unit := do
  if ptr.isImmediate then return
  if (← get).contains ptr then return
  if (← read).visited.contains ptr then throw s!"Cycle detected at {repr ptr}"
  else ExtractM.withVisited ptr do
    match (← read).store.find? ptr with
    | none => throw s!"{repr ptr} not found"
    | some none => modify (·.insert ptr none)
    | some $ some expr =>
      modify (·.insert ptr (some expr))
      match expr with
      | .cons x y | .strCons x y | .symCons x y => loadExprs x; loadExprs y
      | .comm _ x => loadExprs x
      | .nil => loadExprs ⟨.sym, ptr.val⟩

def loadComms (comms : Array F) : ExtractM Unit :=
  comms.forM (loadExprs ⟨.comm, ·⟩)

def LDONHashState.extractComms (stt : LDONHashState) (comms : Array F) :
    Except String Store :=
  match StateT.run (ReaderT.run (loadComms comms) ⟨stt.store, default⟩) default with
  | (.ok _, store) => return store
  | (.error e, _) => throw e

end Scalar

open Scalar

@[inline] def LDON.hide (ldon : LDON) (secret : F) (stt : LDONHashState) :
    F × LDONHashState :=
  StateT.run (hideLDON secret ldon) stt

@[inline] def LDON.commit (ldon : LDON) (stt : LDONHashState) : F × LDONHashState :=
  StateT.run (hideLDON (.ofNat 0) ldon) stt

end Lurk
