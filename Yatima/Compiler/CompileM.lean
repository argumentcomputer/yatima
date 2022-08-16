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
  store  : Ipld.Store
  consts : Array Const
  cache  : RBMap Name (ConstCid × ConstIdx) compare
  deriving Inhabited

/-- Creates a summary off of a `Yatima.Compiler.CompileState` as a `String` -/
def CompileState.summary (s : CompileState) : String :=
  let consts := ", ".intercalate $ s.consts.toList.map
    fun c => s!"{c.name} : {c.ctorName}"
  "Compilation summary:\n" ++
  s!"-----------Constants-----------\n" ++
  s!"{consts}\n" ++
  s!"-------------Sizes-------------\n" ++
  s!"  univ_anon  size: {s.store.univ_anon.size}\n" ++
  s!"  univ_meta  size: {s.store.univ_meta.size}\n" ++
  s!"  expr_anon  size: {s.store.expr_anon.size}\n" ++
  s!"  expr_meta  size: {s.store.expr_meta.size}\n" ++
  s!"  const_anon size: {s.store.const_anon.size}\n" ++
  s!"  const_meta size: {s.store.const_meta.size}\n" ++
  s!"  cache      size: {s.cache.size}"

/--
The type of entries for the `recrCtx`. It contains:
1. The index of the constant in the mutual block
2. The index in the list of weakly equal mutual definitions (N/A inductives)
3. The constant index in array of constants
-/
abbrev RecrCtxEntry := (Nat × Option Nat × ConstIdx)

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
  recrCtx  : Std.RBMap Lean.Name RecrCtxEntry compare
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
  | univ  : Ipld.Both Ipld.Univ  → StoreEntry (Ipld.Both Ipld.UnivCid)
  | expr  : Ipld.Both Ipld.Expr  → StoreEntry (Ipld.Both Ipld.ExprCid)
  | const : Ipld.Both Ipld.Const → StoreEntry (Ipld.Both Ipld.ConstCid)

/-- Adds CID data to the store, but also returns it for practical reasons -/
def addToStore : StoreEntry A → CompileM A
  | .univ  obj =>
    let cid := ⟨ ToIpld.univToCid obj.anon, ToIpld.univToCid obj.meta ⟩
    modifyGet (fun stt => (cid, { stt with store :=
          { stt.store with univ_anon := stt.store.univ_anon.insert cid.anon obj.anon,
                           univ_meta := stt.store.univ_meta.insert cid.meta obj.meta, } }))
  | .expr  obj =>
    let cid := ⟨ ToIpld.exprToCid obj.anon, ToIpld.exprToCid obj.meta ⟩
    modifyGet (fun stt => (cid, { stt with store :=
          { stt.store with expr_anon := stt.store.expr_anon.insert cid.anon obj.anon,
                           expr_meta := stt.store.expr_meta.insert cid.meta obj.meta, } }))
  | .const obj =>
    let cid := ⟨ ToIpld.constToCid obj.anon, ToIpld.constToCid obj.meta ⟩
    match obj.anon, obj.meta with
    -- Mutual definition/inductive blocks do not get added to the set of constants
    | .mutDefBlock .., .mutDefBlock ..
    | .mutIndBlock .., .mutIndBlock .. =>
      modifyGet fun stt => (cid, { stt with store :=
        { stt.store with const_anon := stt.store.const_anon.insert cid.anon obj.anon,
                         const_meta := stt.store.const_meta.insert cid.meta obj.meta } })
    | _, _ =>
      modifyGet fun stt => (cid, { stt with store :=
        { stt.store with const_anon := stt.store.const_anon.insert cid.anon obj.anon,
                         const_meta := stt.store.const_meta.insert cid.meta obj.meta,
                         consts     := stt.store.consts.insert cid } })

/-- Adds data to the cache associated to a name -/
def addToCache (name : Name) (c : ConstCid × ConstIdx) : CompileM Unit := do
  modify fun stt => { stt with cache := stt.cache.insert name c }

/-- Adds a constant to the array of constants at a given index -/
def addToConsts (idx : ConstIdx) (c : Const) : CompileM Unit := do
  let consts := (← get).consts
  if h : idx < consts.size then
    modify fun stt => { stt with consts := consts.set ⟨idx, h⟩ c }
  else
    throw $ .invalidDereferringIndex idx consts.size

end Yatima.Compiler
