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

def Context.find? (ctx : Context) (constName : Name) : Option Const :=
  ctx.store.find? (fun const => const.name == constName)

inductive CheckError where
  | notPi : CheckError
  | notTyp : CheckError
  | valueMismatch : CheckError
  | cannotInferLam : CheckError
  | typNotStructure : CheckError
  | projEscapesProp : CheckError
  | unsafeDefinition : CheckError
  -- Unsafe definition found
  | hasNoRecursionRule : CheckError
  -- Constructor has no associated recursion rule. Implementation is broken.
  | cannotApply : CheckError
  -- Cannot apply argument list to type. Implementation broken.
  | impossibleEqualCase : CheckError
  -- Impossible equal case
  | impossibleProjectionCase : CheckError
  -- Impossible case on projections
  | impossibleEvalCase : CheckError
  -- Cannot evaluate this quotient
  | cannotEvalQuotient : CheckError
  -- Out of the thunk list range
  | outOfRangeError : CheckError
  -- Unknown constant name
  | unknownConst : CheckError
  -- No way to extract a name
  | noName : CheckError
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
