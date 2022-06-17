import Lean
import Std
import Yatima.Env
import Yatima.Graph.Graph

namespace Yatima.Compiler

open Std (RBMap) in
structure CompileState where
  env   : Yatima.Env
  cache : RBMap Name Const Ord.compare

instance : Inhabited CompileState where
  default := ⟨default, .empty⟩

open Std (RBMap HashMap) in
structure CompileEnv where
  constMap : Lean.ConstMap
  univCtx  : List Lean.Name
  bindCtx  : List Name
  cycles   : RBMap Lean.Name (List Lean.Name) compare
  mutOrder : List Lean.Name
  deriving Inhabited

abbrev CompileM := ReaderT CompileEnv $ EStateM String CompileState

def CompileM.run (env : CompileEnv) (ste : CompileState) (m : CompileM α) : Except String Env :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ ste  => .ok ste.env
  | .error e _ => .error e

def withName (name : Name) : CompileM α → CompileM α :=
  withReader $ fun e =>
    ⟨e.constMap, e.univCtx, name :: e.bindCtx, e.cycles, e.mutOrder⟩

def withResetCompileEnv (levels : List Lean.Name) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, levels, [], e.cycles, []⟩

def withOrder (order : List Lean.Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.univCtx, e.bindCtx, e.cycles, order⟩

end Yatima.Compiler
