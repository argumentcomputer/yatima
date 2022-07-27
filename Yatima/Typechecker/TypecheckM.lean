import Yatima.Typechecker.Value

namespace Yatima.Typechecker

structure Context where
  lvl   : Nat
  env   : Env Value
  types : List (Thunk Value)
  store : Array Const
  deriving Inhabited

def Context.init (store : Array Const) : Context :=
  { (default : Context) with store := store }

inductive CheckError where
  | notPi : CheckError
  | notTyp : CheckError
  | valueMismatch : CheckError
  | cannotInferLam : CheckError
  | typNotStructure : CheckError
  | projEscapesProp : CheckError
  -- Unsafe definition found
  | unsafeDefinition : CheckError
  -- Constructor has no associated recursion rule. Implementation is broken.
  | hasNoRecursionRule : CheckError
  -- Cannot apply argument list to type. Implementation broken.
  | cannotApply : CheckError
  -- Impossible equal case
  | impossibleEqualCase : CheckError
  -- Impossible case on projections
  | impossibleProjectionCase : CheckError
  -- Cannot apply arguments to something other than a lambda or partial application
  | impossibleApplyCase : CheckError
  -- Cannot evaluate this quotient
  | cannotEvalQuotient : CheckError
  -- Out of the thunk list range
  | outOfRangeError : CheckError
  -- Out of the range of definitions
  | outOfDefnRange : CheckError
  | impossible : CheckError
  deriving Inhabited

abbrev TypecheckM := ReaderT Context $ ExceptT CheckError Id

def TypecheckM.run (ctx : Context) (m : TypecheckM α) : Except CheckError α :=
  ExceptT.run (ReaderT.run m ctx)

-- TODO: drop this panicking function
def TypecheckM.run! [Inhabited α] (ctx : Context) (str : String) (m : TypecheckM α) : α :=
  match TypecheckM.run ctx m with
  | .ok a => a
  | _ => panic! str

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
