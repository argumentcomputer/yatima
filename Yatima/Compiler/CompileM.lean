import Yatima.Datatypes.Store
import Yatima.Compiler.CompileError
import Yatima.Ipld.ToIpld
import Yatima.Compiler.Utils

namespace Yatima.Compiler

open Std (RBMap)

/--
The state for the `Yatima.Compiler.CompileM` monad.

* `store` contains the resulting set of objects in the IPLD format
* `consts` is the "pure" array of constants, without CIDs
* `cache` is just for optimization purposes
-/
structure CompileState where
  irStore   : IR.Store
  tcStore   : TC.Store
  ipldStore : Ipld.Store
  cache     : RBMap Name (IR.BothConstCid × TC.ConstIdx) compare
  deriving Inhabited

/-- Creates a summary off of a `Yatima.Compiler.CompileState` as a `String` -/
def CompileState.summary (s : CompileState) : String :=
  let consts := ", ".intercalate $ s.tcStore.consts.toList.map
    fun c => s!"{c.name} : {c.ctorName}"
  "Compilation summary:\n" ++
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
The read-only environment for the `Yatima.Compiler.CompileM` monad.

* `constMap` is the original set of constants provided by Lean
* `univCtx` is the current list of universes
* `bindCtx` is the current list of binders
* `recrCtx` is keeps the information for names that represent recursive calls
* `log` tells whether the user wants to log the compilation
-/
structure CompileEnv where
  constMap : Lean.ConstMap
  univCtx  : List Name
  bindCtx  : List Name
  recrCtx  : Std.RBMap Name RecrCtxEntry compare
  log      : Bool
  deriving Inhabited

/-- Instantiates a `Yatima.Compiler.CompileEnv` from a map of constants -/
def CompileEnv.init (map : Lean.ConstMap) (log : Bool) : CompileEnv :=
  ⟨map, [], [], .empty, log⟩

/--
The monad in which compilation takes place is a stack of `ReaderT`, `ExceptT`
and `StateT` on top of IO
-/
abbrev CompileM := ReaderT CompileEnv $
  ExceptT CompileError $ StateT CompileState IO

/-- Basic runner function for `Yatima.Compiler.CompileEnv` -/
def CompileM.run (env : CompileEnv) (ste : CompileState) (m : CompileM α) :
    IO $ Except CompileError CompileState := do
  match ← StateT.run (ReaderT.run m env) ste with
  | (.ok _,  ste) => return .ok ste
  | (.error e, _) => return .error e

/-- Computes with a new binder in the monad environment -/
def withBinder (name : Name) : CompileM α → CompileM α :=
  withReader $ fun e =>
    ⟨e.constMap, e.univCtx, name :: e.bindCtx, e.recrCtx, e.log⟩

/-- Computes with a given list of levels and reset binders and `recrCtx` -/
def withLevelsAndReset (levels : List Name) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, levels, [], .empty, e.log⟩

/-- Computes with a given `recrCtx` -/
def withRecrs (recrCtx : RBMap Name RecrCtxEntry compare) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.univCtx, e.bindCtx, recrCtx, e.log⟩

/-- Computes with a given list of levels-/
def withLevels (lvls : List Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, lvls, e.bindCtx, e.recrCtx, e.log⟩

/-- Possibly gets a `Yatima.Compiler.RecrCtxEntry` from the `recrCtx` by name -/
def getFromRecrCtx (name : Name) : CompileM $ Option RecrCtxEntry :=
  return (← read).recrCtx.find? name

/-- Forcibly gets a `Yatima.Compiler.RecrCtxEntry` from the `recrCtx` by name -/
def getFromRecrCtx! (name : Name) : CompileM $ RecrCtxEntry := do
  match ← getFromRecrCtx name with
  | some entry => pure entry
  | none => throw $ .notFoundInRecrCtx name

/-- Auxiliary type to standardize additions of CIDs to the store -/
inductive StoreEntry : Type → Type
  | univ  : IR.Both IR.Univ  → StoreEntry (IR.BothUnivCid)
  | expr  : IR.Both IR.Expr  → StoreEntry (IR.BothExprCid)
  | const : IR.Both IR.Const → StoreEntry (IR.BothConstCid)

open Ipld in
/-- Adds CID data to the store, but also returns it for practical reasons -/
def addToStore : StoreEntry A → CompileM A
  | .univ obj =>
    let (ipldAnon, cidAnon) := univToCid obj.anon
    let (ipldMeta, cidMeta) := univToCid obj.meta
    modifyGet fun stt => (⟨cidAnon, cidMeta⟩, { stt with
      irStore := { stt.irStore with
        univAnon := stt.irStore.univAnon.insert cidAnon obj.anon,
        univMeta := stt.irStore.univMeta.insert cidMeta obj.meta }
      ipldStore := { stt.ipldStore with
        univAnon := stt.ipldStore.univAnon.push $ .array #[.link cidAnon.data, ipldAnon]
        univMeta := stt.ipldStore.univMeta.push $ .array #[.link cidMeta.data, ipldMeta] } })
  | .expr obj =>
    let (ipldAnon, cidAnon) := exprToCid obj.anon
    let (ipldMeta, cidMeta) := exprToCid obj.meta
    modifyGet fun stt => (⟨cidAnon, cidMeta⟩, { stt with
      irStore := { stt.irStore with
        exprAnon := stt.irStore.exprAnon.insert cidAnon obj.anon,
        exprMeta := stt.irStore.exprMeta.insert cidMeta obj.meta }
      ipldStore := { stt.ipldStore with
        exprAnon := stt.ipldStore.exprAnon.push $ .array #[.link cidAnon.data, ipldAnon]
        exprMeta := stt.ipldStore.exprMeta.push $ .array #[.link cidMeta.data, ipldMeta] } })
  | .const obj =>
    let (ipldAnon, cidAnon) := constToCid obj.anon
    let (ipldMeta, cidMeta) := constToCid obj.meta
    let cid := ⟨cidAnon, cidMeta⟩
    match obj.anon, obj.meta with
    -- Mutual definition/inductive blocks do not get added to the set of constants
    | .mutDefBlock .., .mutDefBlock ..
    | .mutIndBlock .., .mutIndBlock .. =>
      modifyGet fun stt => (cid, { stt with
        irStore := { stt.irStore with
          constAnon := stt.irStore.constAnon.insert cidAnon obj.anon,
          constMeta := stt.irStore.constMeta.insert cidMeta obj.meta }
        ipldStore := { stt.ipldStore with
          constAnon := stt.ipldStore.constAnon.push $ .array #[.link cidAnon.data, ipldAnon]
          constMeta := stt.ipldStore.constMeta.push $ .array #[.link cidMeta.data, ipldMeta] } })
    | _, _ =>
      modifyGet fun stt => (cid, { stt with
        irStore := { stt.irStore with
          constAnon := stt.irStore.constAnon.insert cidAnon obj.anon,
          constMeta := stt.irStore.constMeta.insert cidMeta obj.meta,
          consts    := stt.irStore.consts.insert cid }
        ipldStore := { stt.ipldStore with
          constAnon := stt.ipldStore.constAnon.push $ .array #[.link cidAnon.data, ipldAnon]
          constMeta := stt.ipldStore.constMeta.push $ .array #[.link cidMeta.data, ipldMeta]
          consts    := stt.ipldStore.consts.push    $ .array #[.link cidAnon.data, .link cidMeta.data] } })

/-- Adds data associated with a name to the cache -/
def addToCache (name : Name) (c : IR.BothConstCid × TC.ConstIdx) : CompileM Unit :=
  modify fun stt => { stt with cache := stt.cache.insert name c }

/-- Adds a constant to the array of constants at a given index -/
def addToConsts (idx : TC.ConstIdx) (c : TC.Const) : CompileM Unit := do
  let tcStore := (← get).tcStore
  let consts := tcStore.consts
  if h : idx < consts.size then
    modify fun stt =>
      { stt with tcStore := { tcStore with consts := consts.set ⟨idx, h⟩ c } }
  else
    throw $ .invalidConstantIndex idx consts.size

end Yatima.Compiler
