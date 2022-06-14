import Lean
import Std
import Yatima.Env

namespace Yatima.Compiler.CompileM

open Std (RBMap) in
structure CompileState where
  env   : Yatima.Env
  cache : RBMap Name Const Ord.compare

instance : Inhabited CompileState where
  default := ⟨default, .empty⟩

structure CompileEnv where
  constMap : Lean.ConstMap
  bindCtx  : List Name
  deriving Inhabited

abbrev CompileM := ReaderT CompileEnv $ EStateM String CompileState

def bind (name: Name): CompileM α → CompileM α :=
  withReader fun e => ⟨e.constMap, name :: e.bindCtx⟩

def CompileM.run (env: CompileEnv) (ste: CompileState) (m : CompileM α) : Except String Env :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ ste  => .ok ste.env
  | .error e _ => .error e

end Yatima.Compiler.CompileM
