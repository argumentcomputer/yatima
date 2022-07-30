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

inductive CheckError where
  | notPi : Value → CheckError
  | notTyp : Value → CheckError
  | valueMismatch : Value → Value → CheckError
  | cannotInferLam : CheckError
  | typNotStructure : Value → CheckError
  | projEscapesProp : Expr → CheckError
  | unsafeDefinition : CheckError
  | hasNoRecursionRule : CheckError
  | cannotApply : CheckError
  | outOfRangeError : Name → Nat → Nat → CheckError
  | outOfContextRange : Name → Nat → Nat → CheckError
  | outOfDefnRange : Name → Nat → Nat → CheckError
  | impossible : CheckError
  | custom : String → CheckError
  deriving Inhabited
  
instance : ToString CheckError where
  toString 
  | .notPi val => s!"Expected a pi type, found {printVal val}"
  | .notTyp val => s!"Expected a sort type, found {printVal val}"
  | .valueMismatch val₁ val₂ => s!"Expected a {printVal val₁}, found {printVal val₂}"
  | .cannotInferLam .. => "Cannot infer the type of a lambda term"
  | .typNotStructure val => s!"Expected a structure type, found {printVal val}"
  | .projEscapesProp term => s!"Projection {printExpr term} not allowed"
  | .unsafeDefinition .. => "Unsafe definition found"
  | .hasNoRecursionRule .. => "Constructor has no associated recursion rule. Implementation is broken."
  | .cannotApply .. => "Cannot apply argument list to type. Implementation broken."
  | .outOfRangeError name idx len => s!"'{name}' (index {idx}) out of the thunk list range (size {len})"
  | .outOfDefnRange name idx len => s!"'{name}' (index {idx}) out of the range of definitions (size {len})"
  | .outOfContextRange name idx len => s!"'{name}' (index {idx}) out of context range (size {len})"
  | .impossible .. => "Impossible case. Implementation broken."
  | .custom str => str

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
