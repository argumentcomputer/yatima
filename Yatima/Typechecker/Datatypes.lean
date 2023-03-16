import Yatima.Datatypes.Const

namespace Yatima.Typechecker

/-!
# Basic concepts

* Expressions are objects to be evaluated given an appropriate environment
* Values are the result of evaluating (reducing, normalizing) expressions in a
environment
* Finally, environments map free variables of expressions to values

When we talk about "unevaluated expressions", you should think of these
expression/environment pairs. They are also called *closures*
-/

open IR

open Lurk (F)

/-- Typed expressions are expressions that have been processed by the typechecker -/
inductive TypedExpr
  | var   : Nat → TypedExpr
  | sort  : Univ → TypedExpr
  -- NOTE: F here represents a hash of a normal `IR.Const`, as that is how we index into `TypecheckState.typedConsts`
  | const : F → List Univ → TypedExpr
  | app   : TypedExpr → TypedExpr → TypedExpr
  | lam   : TypedExpr → TypedExpr → TypedExpr
  | pi    : TypedExpr → TypedExpr → TypedExpr
  | letE  : TypedExpr → TypedExpr → TypedExpr → TypedExpr
  | lit   : Literal → TypedExpr
  | proj  : F → Nat → TypedExpr → TypedExpr
  deriving BEq, Inhabited

/--
Remove all binders from an expression, converting a lambda into
an "implicit lambda". This is useful for constructing the `rhs` of
recursor rules.
-/
def TypedExpr.toImplicitLambda : TypedExpr → TypedExpr
  | .lam _ body => toImplicitLambda body
  | x => x

inductive TypedConst
  | «axiom»     : (type : TypedExpr) → TypedConst
  | «theorem»   : (type deref : TypedExpr) → TypedConst
  | «inductive» : (type : TypedExpr) → (struct : Bool) → TypedConst
  | «opaque»    : (type value : TypedExpr) → TypedConst
  | definition  : (type deref : TypedExpr) → (part : Bool) → TypedConst
  | constructor : (type : TypedExpr) → (idx fields : Nat) → TypedConst
  | recursor    : (type : TypedExpr) → (params motives minors indices : Nat) → (k : Bool) → (indProj : InductiveProj) → (rules : Array (Nat × TypedExpr)) → TypedConst
  | quotient    : (type : TypedExpr) → (kind : QuotKind) → TypedConst
  deriving Inhabited, BEq

def TypedConst.type : TypedConst → TypedExpr
  | «axiom»     type ..
  | «theorem»   type ..
  | «inductive» type ..
  | «opaque»    type ..
  | definition  type ..
  | constructor type ..
  | recursor    type ..
  | quotient    type .. => type

structure Env' (SusValue : Type) where
  exprs : List SusValue
  univs : List Univ
  deriving Inhabited

mutual
  /--
  Values are the final result of the evaluation of well-typed expressions under a well-typed
  environment.
  -/
  inductive Value
    /-- Type universes. It is assumed `Univ` is reduced/simplified -/
    | sort : Univ → Value
    /-- Values can only be an application if its a stuck application. That is, if
    the head of the application is neutral -/
    | app : Neutral → List (Thunk Value) → Value
    /-- Lambdas are unevaluated expressions with environments for their free
    variables apart from their argument variables -/
    | lam : Thunk Value → TypedExpr → Env' (Thunk Value) → Value
    /-- Pi types will have thunks for their domains and unevaluated expressions
    analogous to lambda bodies for their codomains -/
    | pi : Thunk Value → TypedExpr → Env' (Thunk Value) → Value
    | lit : Literal → Value
    -- An exception constructor is used to catch bugs in the evaluator/typechecker
    | exception : String → Value
    deriving Inhabited
  /--
  A neutral term is either a variable or a constant with not enough arguments to
  reduce. They appear as the head of a stuck application.
  -/
  inductive Neutral
    | fvar  : Nat → Neutral
    | const : F → List Univ → Neutral
    | proj  : F → Nat → Value → Neutral
    deriving Inhabited

end

/--
Suspended values are thunks that return a value
-/
abbrev SusValue := Thunk Value

/--
The environment will bind free variables to different things, depending on
the evaluation strategy:

1) Strict evaluation: binds free variables to values
2) Non-strict evaluation: binds free variables to unevaluated expressions
3) Lazy evaluation (i.e. non-strict without duplication of work): binds free variables to thunks

Here we chose lazy evaluation since it is more efficient for typechecking.

Since we also have universes with free variables, we need to add a environment
for universe variables as well
-/
abbrev Env := Env' SusValue

/-- The arguments of a stuck sequence of applications `(h a1 ... an)` -/
abbrev Args := List SusValue

instance : Inhabited SusValue where
  default := {fn := default}

def Value.neu (neu : Neutral) : Value := .app neu []

def Value.ctorName : Value → String
  | .sort      .. => "sort"
  | .app       .. => "app"
  | .lam       .. => "lam"
  | .pi        .. => "pi"
  | .lit       .. => "lit"
  | .exception .. => "exception"

def Neutral.ctorName : Neutral → String
  | .fvar  .. => "fvar"
  | .const .. => "const"
  | .proj  .. => "proj"

namespace Env'
/-- Stacks a new expression in the environment -/
def extendWith (env : Env) (thunk : SusValue) : Env :=
  .mk (thunk :: env.exprs) env.univs

/-- Sets a list of expressions to a environment -/
def withExprs (env : Env) (exprs : List SusValue) : Env :=
  .mk exprs env.univs

end Env'

/-- Creates a new constant with a name, a constant index and an universe list -/
def mkConst (f : F) (univs : List Univ) : Value :=
  .neu (.const f univs)

/-- Creates a new variable as a thunk -/
def mkSusVar (idx : Nat) : SusValue :=
  .mk fun _ => .neu (.fvar idx)

inductive PrimConstOp
  | natAdd | natMul | natPow | natBeq | natBle | natBlt  | natSucc
  deriving Ord, Repr

inductive PrimConst
  | nat
  | bool
  | natZero
  | boolTrue
  | boolFalse
  | string
  | op : PrimConstOp → PrimConst
  deriving Ord, Repr

def PrimConstOp.numArgs : PrimConstOp → Nat
  | .natAdd | .natMul | .natPow | .natBeq | .natBle | .natBlt => 2 | .natSucc => 1

def PrimConstOp.reducible : PrimConstOp → Bool
  | .natAdd | .natMul | .natPow | .natBeq | .natBlt | .natBle => true | .natSucc => false

instance : ToString PrimConst where toString
  | .nat         => "Nat"
  | .bool        => "Bool"
  | .boolTrue    => "Bool.true"
  | .boolFalse   => "Bool.false"
  | .natZero     => "Nat.zero"
  | .string      => "String"
  | .op .natAdd  => "Nat.add"
  | .op .natMul  => "Nat.mul"
  | .op .natPow  => "Nat.pow"
  | .op .natBeq  => "Nat.beq"
  | .op .natBle  => "Nat.ble"
  | .op .natBlt  => "Nat.blt"
  | .op .natSucc => "Nat.succ"

end Yatima.Typechecker
