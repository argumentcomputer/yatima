import Yatima.Store
import Yatima.Compiler.Utils

namespace Yatima.Compiler

open Std (RBMap)

structure CompileState where
  store     : Yatima.Store
  cache     : RBMap Name (ConstCid × Const) compare
  mutDefIdx : RBMap Name Nat compare
  deriving Inhabited

namespace CompileState

def union (s s' : CompileState) :
    Except String CompileState := Id.run do
  let mut cache := s.cache
  for (n, c') in s'.cache do
    match s.cache.find? n with
    | some c₁ =>
      if c₁.1 != c'.1 then return throw s!"Conflicting declarations for '{n}'"
    | none => cache := cache.insert n c'
  return .ok ⟨
    s.store.union s'.store,
    cache,
    s'.mutDefIdx.fold (init := s.mutDefIdx) fun acc n i =>
      acc.insert n i
  ⟩

def summary (s : CompileState) : String :=
  let consts := ", ".intercalate $ s.store.const_cache.toList.map
    fun (_, c) => s!"{c.name} : {c.ctorName}"
  "Compilation state:\n" ++
  s!"----------------------------\n" ++
  s!"{consts}\n" ++
  s!"----------------------------\n" ++
  s!"  univ_cache size: {s.store.univ_cache.size}\n" ++
  s!"  expr_cache size: {s.store.expr_cache.size}\n" ++
  s!"  const_cache size: {s.store.const_cache.size}\n" ++
  s!"  cache size: {s.cache.size}"

end CompileState

structure CompileEnv where
  constMap : Lean.ConstMap
  univCtx  : List Lean.Name
  bindCtx  : List Name
  recrCtx  : Std.RBMap Lean.Name Nat compare
  log      : Bool
  deriving Inhabited

abbrev CompileM := ReaderT CompileEnv $ EStateM String CompileState

def CompileM.run (env : CompileEnv) (ste : CompileState) (m : CompileM α) :
    Except String CompileState :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ ste  => .ok ste
  | .error e _ => .error e

def withName (name : Name) : CompileM α → CompileM α :=
  withReader $ fun e =>
    ⟨e.constMap, e.univCtx, name :: e.bindCtx, e.recrCtx, e.log⟩

def withResetCompileEnv (levels : List Lean.Name) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, levels, [], .empty, e.log⟩

def withRecrs (recrCtx : RBMap Lean.Name Nat compare) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.univCtx, e.bindCtx, recrCtx, e.log⟩

def withLevels (lvls : List Lean.Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, lvls, e.bindCtx, e.recrCtx, e.log⟩

inductive StoreEntry
  | univ_cache  : UnivCid × Univ                             → StoreEntry
  | expr_cache  : ExprCid × Expr                             → StoreEntry
  | const_cache : ConstCid × Const                           → StoreEntry
  | univ_anon   : (Ipld.UnivCid .Anon) × (Ipld.Univ .Anon)   → StoreEntry
  | expr_anon   : (Ipld.ExprCid .Anon) × (Ipld.Expr .Anon)   → StoreEntry
  | const_anon  : (Ipld.ConstCid .Anon) × (Ipld.Const .Anon) → StoreEntry
  | univ_meta   : (Ipld.UnivCid .Meta) × (Ipld.Univ .Meta)   → StoreEntry
  | expr_meta   : (Ipld.ExprCid .Meta) × (Ipld.Expr .Meta)   → StoreEntry
  | const_meta  : (Ipld.ConstCid .Meta) × (Ipld.Const .Meta) → StoreEntry

instance : Coe (UnivCid × Univ) StoreEntry where coe := .univ_cache
instance : Coe (ExprCid × Expr) StoreEntry where coe := .expr_cache
instance : Coe (ConstCid × Const) StoreEntry where coe := .const_cache
instance : Coe ((Ipld.UnivCid .Anon) × (Ipld.Univ .Anon)) StoreEntry where coe := .univ_anon
instance : Coe ((Ipld.ExprCid .Anon) × (Ipld.Expr .Anon)) StoreEntry where coe := .expr_anon
instance : Coe ((Ipld.ConstCid .Anon) × (Ipld.Const .Anon)) StoreEntry where coe := .const_anon
instance : Coe ((Ipld.UnivCid .Meta) × (Ipld.Univ .Meta)) StoreEntry where coe := .univ_meta
instance : Coe ((Ipld.ExprCid .Meta) × (Ipld.Expr .Meta)) StoreEntry where coe := .expr_meta
instance : Coe ((Ipld.ConstCid .Meta) × (Ipld.Const .Meta)) StoreEntry where coe := .const_meta

def addToStore (y : StoreEntry) : CompileM Unit := do
  let stt ← get
  let store := stt.store
  match y with
  | .univ_cache  (cid, obj) => set { stt with store :=
    { store with univ_cache  := store.univ_cache.insert cid obj  } }
  | .univ_anon   (cid, obj) => set { stt with store :=
    { store with univ_anon   := store.univ_anon.insert cid obj   } }
  | .univ_meta   (cid, obj) => set { stt with store :=
    { store with univ_meta   := store.univ_meta.insert cid obj   } }
  | .expr_cache  (cid, obj) => set { stt with store :=
    { store with expr_cache  := store.expr_cache.insert cid obj  } }
  | .expr_anon   (cid, obj) => set { stt with store :=
    { store with expr_anon   := store.expr_anon.insert cid obj   } }
  | .expr_meta   (cid, obj) => set { stt with store :=
    { store with expr_meta   := store.expr_meta.insert cid obj   } }
  | .const_cache (cid, obj) => set { stt with store :=
    { store with const_cache := store.const_cache.insert cid obj } }
  | .const_anon  (cid, obj) => set { stt with store :=
    { store with const_anon  := store.const_anon.insert cid obj  } }
  | .const_meta  (cid, obj) => set { stt with store :=
    { store with const_meta  := store.const_meta.insert cid obj  } }

def addToCache (name : Name) (c : ConstCid × Const) : CompileM Unit := do
  set { ← get with cache := (← get).cache.insert name c }

end Yatima.Compiler
