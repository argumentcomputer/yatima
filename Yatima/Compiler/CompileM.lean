import Yatima.Store
import Yatima.Compiler.Graph

namespace Yatima.Compiler

open Std (RBMap) in
structure CompileState where
  store     : Yatima.Store
  cache     : RBMap Name Const compare
  mutDefIdx : RBMap Lean.Name Nat compare

instance : Inhabited CompileState where
  default := ⟨default, .empty, .empty⟩

open Std (RBMap) in
structure CompileEnv where
  constMap : Lean.ConstMap
  univCtx  : List Lean.Name
  bindCtx  : List Name
  cycles   : Lean.ReferenceMap
  order    : List Lean.Name
  deriving Inhabited

abbrev CompileM := ReaderT CompileEnv $ EStateM String CompileState

def CompileM.run (env : CompileEnv) (ste : CompileState) (m : CompileM α) :
    Except String Store :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ ste  => .ok ste.store
  | .error e _ => .error e

def withName (name : Name) : CompileM α → CompileM α :=
  withReader $ fun e =>
    ⟨e.constMap, e.univCtx, name :: e.bindCtx, e.cycles, e.order⟩

def withResetCompileEnv (levels : List Lean.Name) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, levels, [], e.cycles, []⟩

def withOrder (order : List Lean.Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.univCtx, e.bindCtx, e.cycles, order⟩

def withLevels (lvls : List Lean.Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, lvls, e.bindCtx, e.cycles, e.order⟩

end Yatima.Compiler
