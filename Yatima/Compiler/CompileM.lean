import Lean
import Yatima.Env

namespace Yatima.Compiler.CompileM

structure CompileState where
  env        : Yatima.Env
  deriving Inhabited

structure CompileConfig where 
  ppLean   : Bool
  ppYatima : Bool 
  ppAll    : Bool 
  deriving Inhabited, BEq, Repr
  -- add more options as necessary

def mkConfig (args : List String) : CompileConfig :=
  let ppLean := args.contains "-pl"
  let ppYatima := args.contains "-py"
  ⟨ppLean, ppYatima, ppLean && ppYatima⟩

structure CompileEnv where
  constMap   : Lean.ConstMap
  bindCtx    : List Name
  config     : CompileConfig 
  deriving Inhabited

abbrev CompileM := ReaderT CompileEnv $ EStateM String CompileState

def bind (name: Name): CompileM α → CompileM α :=
  withReader fun e => CompileEnv.mk e.constMap (name :: e.bindCtx) e.config

def CompileM.run (env: CompileEnv) (ste: CompileState) (m : CompileM α) : Except String Env :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ ste  => .ok ste.env
  | .error e _ => .error e

end Yatima.Compiler.CompileM
