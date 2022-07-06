import Yatima.Store
import Yatima.Compiler.Graph

namespace Yatima.Compiler

open Std (RBMap)

structure CompileState where
  store     : Yatima.Store
  cache     : RBMap Name (Const × ConstCid) compare
  mutDefIdx : RBMap Lean.Name Nat compare

def CompileState.union (s s' : CompileState) :
    Except String CompileState := Id.run do
  let mut cache := s.cache
  for (n, c') in s'.cache do
    match s.cache.find? n with
    | some c₁ =>
      if c₁.2 != c'.2 then return throw s!"Conflicting declarations for '{n}'"
    | none => cache := cache.insert n c'
  return .ok ⟨
    s.store.union s'.store,
    cache,
    s'.mutDefIdx.fold (init := s.mutDefIdx) fun acc n i =>
      acc.insert n i
  ⟩

instance : Inhabited CompileState where
  default := ⟨default, .empty, .empty⟩

structure CompileEnv where
  constMap : Lean.ConstMap
  cycles   : Lean.ReferenceMap
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
    ⟨e.constMap, e.cycles, e.univCtx, name :: e.bindCtx, e.recrCtx⟩

def withResetCompileEnv (levels : List Lean.Name) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.cycles, levels, [], .empty⟩

def withRecrs (recrCtx : RBMap Lean.Name Nat compare) : 
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.cycles, e.univCtx, e.bindCtx, recrCtx⟩

def withLevels (lvls : List Lean.Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.cycles, lvls, e.bindCtx, e.recrCtx⟩

end Yatima.Compiler
