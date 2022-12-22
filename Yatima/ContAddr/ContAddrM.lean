import Yatima.Datatypes.Store
import Yatima.ContAddr.ContAddrError
import Yatima.Ipld.ToIpld
import Yatima.Lean.Utils

namespace Yatima.ContAddr

open Std (RBMap)

/--
The state for the `Yatima.ContAddr.ContAddrM` monad.

* `irStore` contains the resulting objects encoded in IR
* `tcStore` contains the resulting objects for typechecking
* `cache` has content-addressed data of constants, accessed by name

The IPLD arrays are used for the later encoding of the IR store in IPLD
-/
structure ContAddrState where
  irStore : IR.Store
  tcStore : TC.Store
  cache   : RBMap Name (IR.BothConstCid × TC.ConstIdx) compare
  constsIpld    : Array Ipld
  univAnonIpld  : Array Ipld
  exprAnonIpld  : Array Ipld
  constAnonIpld : Array Ipld
  univMetaIpld  : Array Ipld
  exprMetaIpld  : Array Ipld
  constMetaIpld : Array Ipld
  univIpldCache  : RBMap (IR.Both IR.Univ)  (Ipld × Ipld × IR.BothUnivCid)  compare
  exprIpldCache  : RBMap (IR.Both IR.Expr)  (Ipld × Ipld × IR.BothExprCid)  compare
  constIpldCache : RBMap (IR.Both IR.Const) (Ipld × Ipld × IR.BothConstCid) compare
  deriving Inhabited

def ContAddrState.ipldStore (s : ContAddrState) : Ipld.Store :=
  ⟨s.constsIpld,
    s.univAnonIpld, s.exprAnonIpld, s.constAnonIpld,
    s.univMetaIpld, s.exprMetaIpld, s.constMetaIpld⟩

/-- Creates a summary off of a `Yatima.ContAddr.ContAddrState` as a `String` -/
def ContAddrState.summary (s : ContAddrState) : String :=
  let consts := ", ".intercalate $ s.tcStore.consts.toList.map
    fun c => s!"{c.name} : {c.ctorName}"
  "Summary:\n" ++
  s!"-----------Constants-----------\n" ++
  s!"{consts}\n" ++
  s!"-------------Sizes-------------\n" ++
  s!"  univ_anon  size: {s.irStore.univAnon.size}\n" ++
  s!"  univ_meta  size: {s.irStore.univMeta.size}\n" ++
  s!"  expr_anon  size: {s.irStore.exprAnon.size}\n" ++
  s!"  expr_meta  size: {s.irStore.exprMeta.size}\n" ++
  s!"  const_anon size: {s.irStore.constAnon.size}\n" ++
  s!"  const_meta size: {s.irStore.constMeta.size}\n" ++
  s!"  cache      size: {s.cache.size}"

/--
The type of entries for the `recrCtx`. It contains:
1. The index of the constant in the mutual block
2. The index in the list of weakly equal mutual definitions (N/A inductives)
3. The constant index in array of constants
-/
abbrev RecrCtxEntry := (Nat × Option Nat × TC.ConstIdx)

/--
The read-only environment for the `Yatima.ContAddr.ContAddrM` monad.

* `constMap` is the original set of constants provided by Lean
* `univCtx` is the current list of universes
* `bindCtx` is the current list of binders
* `recrCtx` is keeps the information for names that represent recursive calls
* `log` tells whether the user wants to log the content-addressing process
-/
structure ContAddrEnv where
  constMap : Lean.ConstMap
  univCtx  : List Name
  bindCtx  : List Name
  recrCtx  : Std.RBMap Name RecrCtxEntry compare
  log      : Bool
  deriving Inhabited

/-- Instantiates a `Yatima.ContAddr.ContAddrEnv` from a map of constants -/
def ContAddrEnv.init (map : Lean.ConstMap) (log : Bool) : ContAddrEnv :=
  ⟨map, [], [], .empty, log⟩

/--
The monad in which content-addressing takes place is a stack of `ReaderT`,
`ExceptT` and `StateT` on top of `IO`
-/
abbrev ContAddrM := ReaderT ContAddrEnv $
  ExceptT ContAddrError $ StateT ContAddrState IO

/-- Basic runner function for `Yatima.ContAddr.ContAddrEnv` -/
def ContAddrM.run (env : ContAddrEnv) (ste : ContAddrState) (m : ContAddrM α) :
    IO $ Except ContAddrError ContAddrState := do
  match ← StateT.run (ReaderT.run m env) ste with
  | (.ok _,  ste) => return .ok ste
  | (.error e, _) => return .error e

/-- Computes with a new binder in the monad environment -/
def withBinder (name : Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun e =>
    ⟨e.constMap, e.univCtx, name :: e.bindCtx, e.recrCtx, e.log⟩

/-- Computes with a given list of levels and reset binders and `recrCtx` -/
def withLevelsAndReset (levels : List Name) :
    ContAddrM α → ContAddrM α :=
  withReader $ fun e => ⟨e.constMap, levels, [], .empty, e.log⟩

/-- Computes with a given `recrCtx` -/
def withRecrs (recrCtx : RBMap Name RecrCtxEntry compare) :
    ContAddrM α → ContAddrM α :=
  withReader $ fun e => ⟨e.constMap, e.univCtx, e.bindCtx, recrCtx, e.log⟩

/-- Computes with a given list of levels-/
def withLevels (lvls : List Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun e => ⟨e.constMap, lvls, e.bindCtx, e.recrCtx, e.log⟩

/-- Possibly gets a `Yatima.ContAddr.RecrCtxEntry` from the `recrCtx` by name -/
def getFromRecrCtx (name : Name) : ContAddrM $ Option RecrCtxEntry :=
  return (← read).recrCtx.find? name

/-- Forcibly gets a `Yatima.ContAddr.RecrCtxEntry` from the `recrCtx` by name -/
def getFromRecrCtx! (name : Name) : ContAddrM $ RecrCtxEntry := do
  match ← getFromRecrCtx name with
  | some entry => pure entry
  | none => throw $ .notFoundInRecrCtx name

/-- Auxiliary type to standardize additions of CIDs to the store -/
inductive StoreEntry : Type → Type
  | univ  : IR.Both IR.Univ  → StoreEntry IR.BothUnivCid
  | expr  : IR.Both IR.Expr  → StoreEntry IR.BothExprCid
  | const : IR.Both IR.Const → StoreEntry IR.BothConstCid

open Ipld

def getUnivIpld (obj : IR.Both IR.Univ) : ContAddrM $ Ipld × Ipld × IR.BothUnivCid := do
  match (← get).univIpldCache.find? obj with
  | some x => pure x
  | none =>
    let (ipldAnon, cidAnon) := univToCid obj.anon
    let (ipldMeta, cidMeta) := univToCid obj.meta
    let data := (ipldAnon, ipldMeta, ⟨cidAnon, cidMeta⟩)
    modifyGet fun stt => (data, { stt with
      univIpldCache := stt.univIpldCache.insert obj data })

def getExprIpld (obj : IR.Both IR.Expr) : ContAddrM $ Ipld × Ipld × IR.BothExprCid := do
  match (← get).exprIpldCache.find? obj with
  | some x => pure x
  | none =>
    let (ipldAnon, cidAnon) := exprToCid obj.anon
    let (ipldMeta, cidMeta) := exprToCid obj.meta
    let data := (ipldAnon, ipldMeta, ⟨cidAnon, cidMeta⟩)
    modifyGet fun stt => (data, { stt with
      exprIpldCache := stt.exprIpldCache.insert obj data })

def getConstIpld (obj : IR.Both IR.Const) : ContAddrM $ Ipld × Ipld × IR.BothConstCid := do
  match (← get).constIpldCache.find? obj with
  | some x => pure x
  | none =>
    let (ipldAnon, cidAnon) := constToCid obj.anon
    let (ipldMeta, cidMeta) := constToCid obj.meta
    let data := (ipldAnon, ipldMeta, ⟨cidAnon, cidMeta⟩)
    modifyGet fun stt => (data, { stt with
      constIpldCache := stt.constIpldCache.insert obj data })

/-- Adds CID data to the store, but also returns it for practical reasons -/
def addToStore : StoreEntry A → ContAddrM A
  | .univ obj => do
    let (ipldAnon, ipldMeta, ⟨cidAnon, cidMeta⟩) ← getUnivIpld obj
    modifyGet fun stt => (⟨cidAnon, cidMeta⟩, { stt with
      irStore := { stt.irStore with
        univAnon := stt.irStore.univAnon.insert cidAnon obj.anon,
        univMeta := stt.irStore.univMeta.insert cidMeta obj.meta }
      univAnonIpld := stt.univAnonIpld.push $ .array #[.link cidAnon.data, ipldAnon]
      univMetaIpld := stt.univMetaIpld.push $ .array #[.link cidMeta.data, ipldMeta] })
  | .expr obj => do
    let (ipldAnon, ipldMeta, ⟨cidAnon, cidMeta⟩) ← getExprIpld obj
    modifyGet fun stt => (⟨cidAnon, cidMeta⟩, { stt with
      irStore := { stt.irStore with
        exprAnon := stt.irStore.exprAnon.insert cidAnon obj.anon,
        exprMeta := stt.irStore.exprMeta.insert cidMeta obj.meta }
      exprAnonIpld := stt.exprAnonIpld.push $ .array #[.link cidAnon.data, ipldAnon]
      exprMetaIpld := stt.exprMetaIpld.push $ .array #[.link cidMeta.data, ipldMeta] })
  | .const obj => do
    let (ipldAnon, ipldMeta, ⟨cidAnon, cidMeta⟩) ← getConstIpld obj
    let cid := ⟨cidAnon, cidMeta⟩
    match obj.anon, obj.meta with
    -- Mutual definition/inductive blocks do not get added to the set of constants
    | .mutDefBlock .., .mutDefBlock ..
    | .mutIndBlock .., .mutIndBlock .. =>
      modifyGet fun stt => (cid, { stt with
        irStore := { stt.irStore with
          constAnon := stt.irStore.constAnon.insert cidAnon obj.anon,
          constMeta := stt.irStore.constMeta.insert cidMeta obj.meta }
        constAnonIpld := stt.constAnonIpld.push $ .array #[.link cidAnon.data, ipldAnon]
        constMetaIpld := stt.constMetaIpld.push $ .array #[.link cidMeta.data, ipldMeta] })
    | _, _ =>
      modifyGet fun stt => (cid, { stt with
        irStore := { stt.irStore with
          constAnon := stt.irStore.constAnon.insert cidAnon obj.anon,
          constMeta := stt.irStore.constMeta.insert cidMeta obj.meta,
          consts    := stt.irStore.consts.insert cid }
        constAnonIpld := stt.constAnonIpld.push $ .array #[.link cidAnon.data, ipldAnon]
        constMetaIpld := stt.constMetaIpld.push $ .array #[.link cidMeta.data, ipldMeta]
        constsIpld    := stt.constsIpld.push    $ .array #[.link cidAnon.data, .link cidMeta.data] })

/-- Adds data associated with a name to the cache -/
def addToCache (name : Name) (c : IR.BothConstCid × TC.ConstIdx) : ContAddrM Unit :=
  modify fun stt => { stt with cache := stt.cache.insert name c }

/-- Adds a constant to the array of constants at a given index -/
def addToConsts (idx : TC.ConstIdx) (c : TC.Const) : ContAddrM Unit := do
  let tcStore := (← get).tcStore
  let consts := tcStore.consts
  if h : idx < consts.size then
    modify fun stt =>
      { stt with tcStore := { tcStore with consts := consts.set ⟨idx, h⟩ c } }
  else
    throw $ .invalidConstantIndex idx consts.size

end Yatima.ContAddr
