import Yatima.Typechecker.Datatypes
import Yatima.Typechecker.Printing

namespace Yatima.Typechecker

structure Context where
  lvl   : Nat
  env   : Env
  types : List (Thunk Value)
  store : Array Const
  deriving Inhabited

def Context.init (store : Array Const) : Context :=
  { (default : Context) with store }

def Context.initEnv (env : Env) (store : Array Const) : Context :=
  { (default : Context) with store, env }

abbrev TypecheckM := ReaderT Context $ ExceptT TypecheckError Id

def TypecheckM.run (ctx : Context) (m : TypecheckM α) : Except TypecheckError α :=
  ExceptT.run (ReaderT.run m ctx)

def withEnv (env : Env) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with env := env }

def withExtendedCtx (val : Thunk Value) (typ : Thunk Value) :
    TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with
    lvl := ctx.lvl + 1,
    types := typ :: ctx.types,
    env := ctx.env.extendWith val }

def withExtendedEnv (thunk : Thunk Value) : TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with env := ctx.env.extendWith thunk }

def withNewExtendedEnv (env : Env) (thunk : Thunk Value) :
    TypecheckM α → TypecheckM α :=
  withReader fun ctx => { ctx with env := env.extendWith thunk }

def withNewExtendedEnvByVar (env : Env) (name : Name) (i : Nat) (type : Thunk Value) :
    TypecheckM α → TypecheckM α :=
  withNewExtendedEnv env (mkVar name i type)

end Yatima.Typechecker
