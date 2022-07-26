import Yatima.Typechecker.Value

namespace Yatima.Typechecker

structure Context where
  lvl   : Nat
  env   : Env Value
  types : List (Thunk Value)
  store : Array Const

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
  | impossible : CheckError
  deriving Inhabited

abbrev CheckM := ReaderT Context <| ExceptT CheckError Id
instance : Monad CheckM :=
  let i := inferInstanceAs (Monad CheckM)
  { pure := i.pure, bind := i.bind }

def CheckM.run (m : CheckM α) (ctx : Context) : Except CheckError α :=
  ExceptT.run (ReaderT.run m ctx)

def CheckM.run! [Inhabited α] (m : CheckM α) (ctx : Context) (str : String) : α :=
  match CheckM.run m ctx with
  | .ok a => a
  | _ => panic! str

def extEnvHelper (env : Env Value) (thunk : Thunk Value) : Env Value :=
  { env with exprs := thunk :: env.exprs }

def extCtx (val : Thunk Value) (typ : Thunk Value)  (m : CheckM α) : CheckM α :=
  withReader (fun ctx => { ctx with lvl := ctx.lvl + 1, types := typ :: ctx.types, env := extEnvHelper ctx.env val }) m

def extEnv (thunk : Thunk Value) : CheckM α → CheckM α :=
  withReader (fun ctx => { ctx with env := extEnvHelper ctx.env thunk })

def withExtEnv (env : Env Value) (thunk : Thunk Value) : CheckM α → CheckM α :=
  withReader (fun ctx => { ctx with env := extEnvHelper env thunk })

def withEnv (env : Env Value) : CheckM α → CheckM α :=
  withReader (fun ctx => { ctx with env := env })

end Yatima.Typechecker
