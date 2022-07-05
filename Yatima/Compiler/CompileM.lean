import Yatima.Store
import Yatima.Compiler.Graph

namespace Yatima.Compiler

open Std (RBMap)

structure CompileState where
  store     : Yatima.Store
  cache     : RBMap Name (Const × ConstCid) compare
  mutDefIdx : RBMap Lean.Name Nat compare

instance : Inhabited CompileState where
  default := ⟨default, .empty, .empty⟩

open Std (RBMap) in
structure CompileEnv where
  constMap : Lean.ConstMap
  cycles   : Lean.ReferenceMap
  univCtx  : List Lean.Name
  bindCtx  : List Name
  recrCtx  : RBMap Lean.Name Nat compare
  deriving Inhabited

abbrev CompileM := ReaderT CompileEnv $ EStateM String CompileState

def CompileM.run (env : CompileEnv) (ste : CompileState) (m : CompileM α) :
    Except String Store :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ ste  => .ok ste.store
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
