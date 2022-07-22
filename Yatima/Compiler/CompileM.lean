import Yatima.Store
import Yatima.ToIpld
import Yatima.Compiler.Utils

namespace Yatima.Compiler

open Std (RBMap)

structure CompileState where
  store     : Ipld.Store
  defns     : Array Const
  cache     : RBMap Name (ConstCid × ConstIdx) compare
  mutDefIdx : RBMap Name Nat compare
  deriving Inhabited

def CompileState.union (s s' : CompileState) :
    Except String CompileState := Id.run do
  let mut cache := s.cache
  for (n, c') in s'.cache do
    match s.cache.find? n with
    | some c₁ =>
      if c₁.1 != c'.1 then return throw s!"Conflicting declarations for '{n}'"
    | none => cache := cache.insert n c'
  return .ok ⟨
    s.store.union s'.store,
    s.defns ++ s'.defns,
    cache,
    s'.mutDefIdx.fold (init := s.mutDefIdx) fun acc n i =>
      acc.insert n i
  ⟩

structure CompileEnv where
  constMap : Lean.ConstMap
  univCtx  : List Lean.Name
  bindCtx  : List Name
  recrCtx  : Std.RBMap Lean.Name (Nat × Nat) compare
  deriving Inhabited

abbrev CompileM := ReaderT CompileEnv $ EStateM String CompileState

def CompileM.run (env : CompileEnv) (ste : CompileState) (m : CompileM α) :
    Except String CompileState :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ ste  => .ok ste
  | .error e _ => .error e

def withName (name : Name) : CompileM α → CompileM α :=
  withReader $ fun e =>
    ⟨e.constMap, e.univCtx, name :: e.bindCtx, e.recrCtx⟩

def withResetCompileEnv (levels : List Lean.Name) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, levels, [], .empty⟩

def withRecrs (recrCtx : RBMap Lean.Name (Nat × Nat) compare) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.univCtx, e.bindCtx, recrCtx⟩

def withLevels (lvls : List Lean.Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, lvls, e.bindCtx, e.recrCtx⟩

inductive StoreKey : Type → Type
  | univ   : Ipld.Both Ipld.UnivCid  → StoreKey (Ipld.Both Ipld.Univ)
  | expr   : Ipld.Both Ipld.ExprCid  → StoreKey (Ipld.Both Ipld.Expr)
  | const  : Ipld.Both Ipld.ConstCid → StoreKey (Ipld.Both Ipld.Const)

def StoreKey.find? : (key : StoreKey A) → CompileM (Option A)
  | .univ  univCid => do
    let store := (← get).store
    match store.univ_anon.find? univCid.anon, store.univ_meta.find? univCid.meta with
    | some univAnon, some univMeta => pure $ some ⟨ univAnon, univMeta ⟩
    | _, _ => pure none
  | .expr  exprCid => do
    let store := (← get).store
    match store.expr_anon.find? exprCid.anon, store.expr_meta.find? exprCid.meta with
    | some exprAnon, some exprMeta => pure $ some ⟨ exprAnon, exprMeta ⟩
    | _, _ => pure none
  | .const constCid => do
    let store := (← get).store
    match store.const_anon.find? constCid.anon, store.const_meta.find? constCid.meta with
    | some constAnon, some constMeta => pure $ some ⟨ constAnon, constMeta ⟩
    | _, _ => pure none

def StoreKey.find! (key : StoreKey A) : CompileM A := do
  let some value ← StoreKey.find? key | throw "Cannot find key in store"
  pure value

inductive StoreValue : Type → Type
  | univ   : Ipld.Both Ipld.Univ  → StoreValue (Ipld.Both Ipld.UnivCid)
  | expr   : Ipld.Both Ipld.Expr  → StoreValue (Ipld.Both Ipld.ExprCid)
  | const  : Ipld.Both Ipld.Const → StoreValue (Ipld.Both Ipld.ConstCid)

def StoreValue.insert : StoreValue A → CompileM A
  | .univ  obj  =>
    let cid  := ⟨ ToIpld.univToCid obj.anon, ToIpld.univToCid obj.meta ⟩
    modifyGet (fun stt => (cid, { stt with store :=
          { stt.store with univ_anon  := stt.store.univ_anon.insert cid.anon obj.anon,
                           univ_meta  := stt.store.univ_meta.insert cid.meta obj.meta } }))
  | .expr  obj  =>
    let cid  := ⟨ ToIpld.exprToCid obj.anon, ToIpld.exprToCid obj.meta ⟩
    modifyGet (fun stt => (cid, { stt with store :=
          { stt.store with expr_anon  := stt.store.expr_anon.insert cid.anon obj.anon,
                           expr_meta  := stt.store.expr_meta.insert cid.meta obj.meta } }))
  | .const obj =>
    let cid  := ⟨ ToIpld.constToCid obj.anon, ToIpld.constToCid obj.meta ⟩
    modifyGet (fun stt => (cid, { stt with store :=
          { stt.store with const_anon := stt.store.const_anon.insert cid.anon obj.anon,
                           const_meta := stt.store.const_meta.insert cid.meta obj.meta } }))

def addToCache (name : Name) (c : ConstCid × ConstIdx) : CompileM Unit := do
  modifyGet (fun stt => ((), { stt with cache := stt.cache.insert name c}))

end Yatima.Compiler
