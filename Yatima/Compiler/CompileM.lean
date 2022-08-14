import Yatima.Datatypes.Store
import Yatima.Compiler.CompileError
import Yatima.Ipld.ToIpld
import Yatima.Compiler.Utils

namespace Yatima.Compiler

open Std (RBMap)

structure CompileState where
  store  : Ipld.Store
  consts : Array Const
  cache  : RBMap Name (ConstCid × ConstIdx) compare
  deriving Inhabited

namespace CompileState

def union (s s' : CompileState) : Except String CompileState := Id.run do
  let mut cache := s.cache
  for (n, c') in s'.cache do
    match s.cache.find? n with
    | some c₁ =>
      if c₁.1 != c'.1 then return throw s!"Conflicting declarations for '{n}'"
    | none => cache := cache.insert n c'
  return .ok ⟨
    s.store.union s'.store,
    s'.consts,
    cache
  ⟩

def summary (s : CompileState) : String :=
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

end CompileState

abbrev RecrCtxEntry := (Nat × Option Nat × Nat)

structure CompileEnv where
  constMap : Lean.ConstMap
  univCtx  : List Lean.Name
  bindCtx  : List Name
  -- (mutual index in recrCtx, weakly equal index (N/A inductives), constant index in array of constants)
  recrCtx  : Std.RBMap Lean.Name RecrCtxEntry compare
  log      : Bool
  deriving Inhabited

def CompileEnv.init (map : Lean.ConstMap) (log : Bool) : CompileEnv :=
  ⟨map, [], [], .empty, log⟩

abbrev CompileM := ReaderT CompileEnv $
  ExceptT CompileError $ StateT CompileState IO

def CompileM.run (env : CompileEnv) (ste : CompileState) (m : CompileM α) :
    IO $ Except CompileError CompileState := do
  match ← StateT.run (ReaderT.run m env) ste with
  | (.ok _,  ste) => return .ok ste
  | (.error e, _) => return .error e

def withName (name : Name) : CompileM α → CompileM α :=
  withReader $ fun e =>
    ⟨e.constMap, e.univCtx, name :: e.bindCtx, e.recrCtx, e.log⟩

def withResetCompileEnv (levels : List Lean.Name) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, levels, [], .empty, e.log⟩

def withRecrs (recrCtx : RBMap Lean.Name RecrCtxEntry compare) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.univCtx, e.bindCtx, recrCtx, e.log⟩

def withLevels (lvls : List Lean.Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, lvls, e.bindCtx, e.recrCtx, e.log⟩

inductive StoreKey : Type → Type
  | univ  : Ipld.Both Ipld.UnivCid  → StoreKey (Ipld.Both Ipld.Univ)
  | expr  : Ipld.Both Ipld.ExprCid  → StoreKey (Ipld.Both Ipld.Expr)
  | const : Ipld.Both Ipld.ConstCid → StoreKey (Ipld.Both Ipld.Const)

def StoreKey.find? (key : StoreKey A) : CompileM (Option A) := do
  let store := (← get).store
  match key with
  | .univ univCid =>
    match store.univ_anon.find? univCid.anon, store.univ_meta.find? univCid.meta with
    | some univAnon, some univMeta => pure $ some ⟨ univAnon, univMeta ⟩
    | _, _ => pure none
  | .expr exprCid =>
    match store.expr_anon.find? exprCid.anon, store.expr_meta.find? exprCid.meta with
    | some exprAnon, some exprMeta => pure $ some ⟨ exprAnon, exprMeta ⟩
    | _, _ => pure none
  | .const constCid =>
    match store.const_anon.find? constCid.anon, store.const_meta.find? constCid.meta with
    | some constAnon, some constMeta => pure $ some ⟨ constAnon, constMeta ⟩
    | _, _ => pure none

def StoreKey.find! (key : StoreKey A) : CompileM A := do
  let some value ← StoreKey.find? key | throw $ .custom "Cannot find key in store"
  return value

inductive StoreValue : Type → Type
  | univ  : Ipld.Both Ipld.Univ  → StoreValue (Ipld.Both Ipld.UnivCid)
  | expr  : Ipld.Both Ipld.Expr  → StoreValue (Ipld.Both Ipld.ExprCid)
  | const : Ipld.Both Ipld.Const → StoreValue (Ipld.Both Ipld.ConstCid)

def StoreValue.insert : StoreValue A → CompileM A
  | .univ  obj  =>
    let cid  := ⟨ ToIpld.univToCid obj.anon, ToIpld.univToCid obj.meta ⟩
    modifyGet (fun stt => (cid, { stt with store :=
          { stt.store with univ_anon := stt.store.univ_anon.insert cid.anon obj.anon,
                           univ_meta := stt.store.univ_meta.insert cid.meta obj.meta, } }))
  | .expr  obj  =>
    let cid  := ⟨ ToIpld.exprToCid obj.anon, ToIpld.exprToCid obj.meta ⟩
    modifyGet (fun stt => (cid, { stt with store :=
          { stt.store with expr_anon := stt.store.expr_anon.insert cid.anon obj.anon,
                           expr_meta := stt.store.expr_meta.insert cid.meta obj.meta, } }))
  | .const obj =>
    let cid  := ⟨ ToIpld.constToCid obj.anon, ToIpld.constToCid obj.meta ⟩
    match obj.anon, obj.meta with
    -- Mutual definition/inductive blocks do not get added to the set of definitions
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

def addToCache (name : Name) (c : ConstCid × ConstIdx) : CompileM Unit := do
  modify fun stt => { stt with cache := stt.cache.insert name c }

def addToConsts (idx : Nat) (c : Const): CompileM Unit := do
  let consts := (← get).consts
  if h : idx < consts.size then
    modify fun stt => { stt with consts := consts.set ⟨idx, h⟩ c }
  else
    throw $ .invalidDereferringIndex idx consts.size

end Yatima.Compiler
