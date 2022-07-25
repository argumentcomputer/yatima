import Yatima.Typechecker.Value

namespace Yatima.Typechecker

structure Context where
  lvl   : Nat
  env   : Env Value
  types : List (Thunk Value)

inductive CheckError where
  | notPi : CheckError
  | notTyp : CheckError
  | valueMismatch : CheckError
  | cannotInferFix : CheckError
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

def mkConst (name : Name) (k : Const) (univs : List Univ) : Value :=
  Value.app (Neutral.const name k univs) []

def extEnv (env : Env Value) (thunk : Thunk Value) : Env Value :=
  { env with exprs := thunk :: env.exprs }

abbrev CheckM := ReaderT Context <| ExceptT CheckError Id

def extCtx (val : Thunk Value) (typ : Thunk Value)  (m : CheckM α) : CheckM α :=
  withReader (fun ctx => { lvl := ctx.lvl + 1, types := typ :: ctx.types, env := extEnv ctx.env val }) m

def checkStructure (ind : Inductive Expr) : CheckM (Constructor Expr) :=
  if ind.recr || ind.indices != 0 then throw .typNotStructure
  else match ind.struct with
  | .some ctor => pure ctor
  | _ => throw .typNotStructure

def extEnvHelper (thunk : Thunk Value) : CheckM Value → CheckM Value :=
  withReader (fun ctx => { ctx with env := extEnv ctx.env thunk })

def withEnv (lexprs : List (Thunk Value)) (lunivs : List Univ) : CheckM α → CheckM α :=
  withReader (fun ctx => { ctx with env := { exprs := lexprs, univs := lunivs } })

def withExprs (lexprs : List (Thunk Value)) : CheckM α → CheckM α :=
  withReader (fun ctx => { ctx with env := { exprs := lexprs, univs := ctx.env.univs } })

end Yatima.Typechecker