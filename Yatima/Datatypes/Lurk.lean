import Lurk.Backend.Expr
import Poseidon.ForLurk
import Std.Data.RBMap

namespace Lurk

/-! placeholder types -/

inductive LDON
  | nil
  | num : F → LDON
  | u64 : UInt64 → LDON
  | char : Char → LDON
  | str : String → LDON
  | sym : String → LDON
  | cons : LDON → LDON → LDON
  deriving Inhabited, Ord

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
  | num : F → ScalarExpr
  | char : F → ScalarExpr
  | nil
  | strNil
  | symNil
  deriving Repr

open Std (RBMap RBSet)

abbrev Store := RBMap ScalarPtr (Option ScalarExpr) compare

def Store.get? (store : Store) : ScalarPtr → Option (Option ScalarExpr)
  | ⟨.num,  x⟩ => return some $ .num  x
  | ⟨.char, x⟩ => return some $ .char x
  | ⟨.str, F.zero⟩ => return some .strNil
  | ⟨.sym, F.zero⟩ => return some .symNil
  | ptr => store.find? ptr

structure LDONHashState where
  store      : Store
  charsCache : RBMap (List Char) ScalarPtr compare
  ldonCache  : RBMap LDON        ScalarPtr compare
  deriving Inhabited

@[inline] def LDONHashState.get? (stt : LDONHashState) (ptr : ScalarPtr) :
    Option (Option ScalarExpr) :=
  stt.store.get? ptr

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
      | .nil =>
        let rootPtr := ⟨.sym, F.zero⟩
        let nilPtr  ← hashChars ['N', 'I', 'L']
        let lurkPtr ← hashChars ['L', 'U', 'R', 'K']
        let symPtr1 ← addExprHash ⟨.sym, hashPtrPair lurkPtr rootPtr⟩ (.symCons lurkPtr rootPtr)
        addExprHash ⟨.nil, hashPtrPair nilPtr symPtr1⟩ (.symCons nilPtr symPtr1)
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
  discard $ addExprHash ⟨.comm, hash⟩ (.comm hash ptr)
  return hash

def LDON.commit (ldon : LDON) (stt : LDONHashState) : F × LDONHashState :=
  StateT.run (hideLDON (.ofNat 0) ldon) stt

structure ExtractCtx where
  store   : Store
  visited : RBSet ScalarPtr compare
  deriving Inhabited

abbrev ExtractM := ReaderT ExtractCtx $ ExceptT String $ StateM Store

@[inline] def withVisited (ptr : ScalarPtr) : ExtractM α → ExtractM α :=
  withReader fun ctx => { ctx with visited := ctx.visited.insert ptr }

partial def loadExprs (ptr : ScalarPtr) : ExtractM Unit := do
  if ptr.isImmediate then return
  if (← get).contains ptr then return
  if (← read).visited.contains ptr then throw s!"Cycle detected at {repr ptr}"
  else withVisited ptr do
    match (← read).store.find? ptr with
    | none => throw s!"{repr ptr} not found"
    | some none => modify (·.insert ptr none)
    | some $ some expr =>
      modify (·.insert ptr (some expr))
      match expr with
      | .cons x y | .strCons x y | .symCons x y => loadExprs x; loadExprs y
      | .comm f x =>
        if f != ptr.val then throw s!"Inconsistent comm pointer: {repr ptr}"
        else loadExprs x
      | _ => pure ()

def loadComms (comms : Array F) : ExtractM Unit :=
  comms.forM (loadExprs ⟨.comm, ·⟩)

def LDONHashState.extractComms (stt : LDONHashState) (comms : Array F) :
    Except String Store :=
  match StateT.run (ReaderT.run (loadComms comms) ⟨stt.store, default⟩) default with
  | (.ok _, store) => return store
  | (.error e, _) => throw e

namespace Backend.Expr

def datumToLDON : Datum → LDON
  | .num  x => .num x
  | .u64  x => .u64 x
  | .char x => .char x
  | .str  x => .str x
  | .sym "NIL" => .nil
  | .sym  x => .sym x
  | .cons x y => .cons (datumToLDON x) (datumToLDON y)

def atomToLDON : Atom → LDON
  | .nil => .nil
  | .t => .sym "T"
  | .num x => .num x
  | .u64 x => .u64 x
  | .str x => .str x
  | .char x => .char x

partial def toLDON : Expr → LDON
  | .atom a => atomToLDON a
  | .sym s => .sym s
  | .env => .cons (.sym "CURRENT-ENV") .nil
  | .op₁ o e => .cons (.sym o.toString) (.cons e.toLDON .nil)
  | .op₂ o e₁ e₂ => .cons (.sym o.toString) $ .cons e₁.toLDON $ .cons e₂.toLDON .nil
  | e@(.begin ..) =>
    .cons (.sym "BEGIN") $ e.telescopeBegin.foldr (.cons ·.toLDON ·) .nil
  | .if a b c => .cons (.sym "IF") $ .cons a.toLDON $ .cons b.toLDON $ .cons c.toLDON .nil
  | .app₀ e => .cons e.toLDON .nil
  | .app f a => .cons f.toLDON (.cons a.toLDON .nil)
  | .lambda s e =>
    let (ss, b) := e.telescopeLam #[s]
    .cons (.sym "LAMBDA") $
      .cons (ss.foldr (fun s acc => .cons (.sym s) acc) .nil) $ .cons b.toLDON .nil
  | .let s v b =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    .cons (.sym "LET") $
      .cons (bs.foldr (fun (s, v) acc =>
          .cons (.cons (.sym s) (.cons v.toLDON .nil)) acc) .nil) $
        .cons b.toLDON .nil
  | .letrec s v b =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    .cons (.sym "LETREC") $
      .cons (bs.foldr (fun (s, v) acc =>
          .cons (.cons (.sym s) (.cons v.toLDON .nil)) acc) .nil) $
        .cons b.toLDON .nil
  | .quote d => .cons (.sym "QUOTE") $ .cons (datumToLDON d) .nil

end Backend.Expr

end Lurk
