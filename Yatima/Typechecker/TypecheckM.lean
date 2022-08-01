import Yatima.Typechecker.Value
import Yatima.Typechecker.Printing

namespace Yatima.Typechecker

structure Context where
  lvl   : Nat
  env   : Env Value
  types : List (Thunk Value)
  store : Array Const
  deriving Inhabited

def Context.init (store : Array Const) : Context :=
  { (default : Context) with store }

def Context.initEnv (env : Env Value) (store : Array Const) : Context :=
  { (default : Context) with store, env }

abbrev TypecheckM := ReaderT Context $ ExceptT CheckError Id

def TypecheckM.run (ctx : Context) (m : TypecheckM α) : Except CheckError α :=
  ExceptT.run (ReaderT.run m ctx)

def extEnvHelper (env : Env Value) (thunk : Thunk Value) : Env Value :=
  { env with exprs := thunk :: env.exprs }

def extCtx (val : Thunk Value) (typ : Thunk Value)  (m : TypecheckM α) : TypecheckM α :=
  withReader (fun ctx => { ctx with lvl := ctx.lvl + 1, types := typ :: ctx.types, env := extEnvHelper ctx.env val }) m

def extEnv (thunk : Thunk Value) : TypecheckM α → TypecheckM α :=
  withReader (fun ctx => { ctx with env := extEnvHelper ctx.env thunk })

def withExtEnv (env : Env Value) (thunk : Thunk Value) : TypecheckM α → TypecheckM α :=
  withReader (fun ctx => { ctx with env := extEnvHelper env thunk })

def withEnv (env : Env Value) : TypecheckM α → TypecheckM α :=
  withReader (fun ctx => { ctx with env := env })

end Yatima.Typechecker
