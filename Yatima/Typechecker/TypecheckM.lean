import Yatima.Typechecker.Datatypes
import Yatima.Typechecker.Printing

namespace Yatima.Typechecker

structure TypecheckEnv where
  lvl   : Nat
  ctx   : Context
  types : List (Thunk Value)
  store : Array Const
  deriving Inhabited

def TypecheckEnv.init (store : Array Const) : TypecheckEnv :=
  { (default : TypecheckEnv) with store }

def TypecheckEnv.initCtx (ctx : Context) (store : Array Const) : TypecheckEnv :=
  { (default : TypecheckEnv) with store, ctx }

abbrev TypecheckM := ReaderT TypecheckEnv $ ExceptT TypecheckError Id

def TypecheckM.run (env : TypecheckEnv) (m : TypecheckM α) : Except TypecheckError α :=
  ExceptT.run (ReaderT.run m env)

def withCtx (ctx : Context) : TypecheckM α → TypecheckM α :=
  withReader fun env => { env with ctx := ctx }

def withExtendedEnv (val typ : Thunk Value) : TypecheckM α → TypecheckM α :=
  withReader fun env => { env with
    lvl := env.lvl + 1,
    types := typ :: env.types,
    ctx := env.ctx.extendWith val }

def withExtendedCtx (thunk : Thunk Value) : TypecheckM α → TypecheckM α :=
  withReader fun env => { env with ctx := env.ctx.extendWith thunk }

def withNewExtendedCtx (ctx : Context) (thunk : Thunk Value) :
    TypecheckM α → TypecheckM α :=
  withReader fun env => { env with ctx := ctx.extendWith thunk }

def withNewExtendedCtxByVar (ctx : Context) (name : Name) (i : Nat) (type : Thunk Value) :
    TypecheckM α → TypecheckM α :=
  withNewExtendedCtx ctx (mkVar name i type)

end Yatima.Typechecker
