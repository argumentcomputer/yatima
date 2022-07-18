import Yatima.Store
import Yatima.Compiler.Utils


namespace Yatima.Compiler

open Std (RBMap)

structure CompileState where
  store     : Yatima.Store
  cache     : RBMap Name (ConstCid × Const) compare
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
    cache,
    s'.mutDefIdx.fold (init := s.mutDefIdx) fun acc n i =>
      acc.insert n i
  ⟩

structure CompileEnv where
  constMap : Lean.ConstMap
  univCtx  : List Lean.Name
  bindCtx  : List Name
  recrCtx  : Std.RBMap Lean.Name Nat compare
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

def withRecrs (recrCtx : RBMap Lean.Name Nat compare) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.univCtx, e.bindCtx, recrCtx⟩

def withLevels (lvls : List Lean.Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, lvls, e.bindCtx, e.recrCtx⟩

inductive YatimaStoreEntry
  | univ_cache  : UnivCid × Univ           → YatimaStoreEntry
  | expr_cache  : ExprCid × Expr           → YatimaStoreEntry
  | const_cache : ConstCid × Const         → YatimaStoreEntry
  | univ_anon   : UnivAnonCid × UnivAnon   → YatimaStoreEntry
  | expr_anon   : ExprAnonCid × ExprAnon   → YatimaStoreEntry
  | const_anon  : ConstAnonCid × ConstAnon → YatimaStoreEntry
  | univ_meta   : UnivMetaCid × UnivMeta   → YatimaStoreEntry
  | expr_meta   : ExprMetaCid × ExprMeta   → YatimaStoreEntry
  | const_meta  : ConstMetaCid × ConstMeta → YatimaStoreEntry

instance : Coe (UnivCid × Univ) YatimaStoreEntry where coe := .univ_cache
instance : Coe (ExprCid × Expr) YatimaStoreEntry where coe := .expr_cache
instance : Coe (ConstCid × Const) YatimaStoreEntry where coe := .const_cache
instance : Coe (UnivAnonCid × UnivAnon) YatimaStoreEntry where coe := .univ_anon
instance : Coe (ExprAnonCid × ExprAnon) YatimaStoreEntry where coe := .expr_anon
instance : Coe (ConstAnonCid × ConstAnon) YatimaStoreEntry where coe := .const_anon
instance : Coe (UnivMetaCid × UnivMeta) YatimaStoreEntry where coe := .univ_meta
instance : Coe (ExprMetaCid × ExprMeta) YatimaStoreEntry where coe := .expr_meta
instance : Coe (ConstMetaCid × ConstMeta) YatimaStoreEntry where coe := .const_meta

def addToStore (y : YatimaStoreEntry) : CompileM Unit := do
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
