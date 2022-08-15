import Yatima.Datatypes.Store
import Yatima.Compiler.Utils
import Yatima.Converter.ConvertError
import YatimaStdLib.RBMap

namespace Yatima

namespace Converter

open Std (RBMap)

abbrev RecrCtx := RBMap (Nat × Option Nat) (Nat × Name) compare

structure ConvertEnv where
  store     : Ipld.Store
  recrCtx   : RecrCtx
  bindDepth : Nat
  deriving Inhabited

def ConvertEnv.init (store : Ipld.Store) : ConvertEnv :=
  ⟨store, default, 0⟩

structure ConvertState where
  univ_cache  : RBMap UnivCid Univ compare
  expr_cache  : RBMap ExprCid Expr compare
  const_cache : RBMap ConstCid ConstIdx compare
  consts      : Array Const
  constsIdx   : RBMap Name ConstIdx compare
  deriving Inhabited

abbrev ConvertM := ReaderT ConvertEnv <| EStateM ConvertError ConvertState

def ConvertM.run (env : ConvertEnv) (ste : ConvertState) (m : ConvertM α) :
    Except ConvertError ConvertState :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ stt  => .ok stt
  | .error e _ => .error e

def ConvertM.unwrap : Option A → ConvertM A :=
  Option.option (throw .ipldError) pure

def withResetBindDepth : ConvertM α → ConvertM α :=
  withReader $ fun e => { e with bindDepth := 0 }

def withRecrs (recrCtx : RecrCtx) : ConvertM α → ConvertM α :=
  withReader $ fun e => { e with recrCtx }

def withNewBind : ConvertM α → ConvertM α :=
  withReader $ fun e => { e with bindDepth := e.bindDepth + 1 }

namespace Converter

namespace Yatima
