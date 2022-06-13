import Lean
import Yatima.Env

namespace Yatima.Compiler.CompileM

structure CompileState where
  env        : Yatima.Env
  deriving Inhabited

structure CompileEnv where
  constMap   : Lean.ConstMap
  bindCtx    : List Name
  deriving Inhabited

abbrev CompileM := ReaderT CompileEnv $ EStateM String CompileState

def bind (name: Name): CompileM α → CompileM α :=
  withReader fun e => CompileEnv.mk e.constMap (name :: e.bindCtx)

def CompileM.run (env: CompileEnv) (ste: CompileState) (m : CompileM α) : Except String Env :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ ste  => .ok ste.env
  | .error e _ => .error e

end Yatima.Compiler.CompileM
