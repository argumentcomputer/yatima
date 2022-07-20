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
  | hasNoRecursionRule : CheckError
  | cannotApply : CheckError
  | impossibleEqualCase : CheckError
  | impossibleProjectioCase : CheckError
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
  else match ind.ctors with
  | [ctor] => pure ctor
  | _ => throw .typNotStructure

end Yatima.Typechecker