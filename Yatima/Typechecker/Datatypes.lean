import Yatima.Datatypes.Const
import Yatima.Typechecker.TypecheckError

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

open TC

/-- 
Representation of propositions involving primitives. These populate the `Value.litProp` variant,
where normal evaluation would otherwise result in an amount of computation proportional to
the size of the primitives involved. The evaluator must *only* produce such values after
the correctness of the statement has been checked. This is enforced by making each variant
also take a proof of the statement (which is not used for any other purpose).
-/
inductive LiteralProp where
  -- Natural number inequality
  | natNEq (v1 v2 : Nat) (h : v1 ≠ v2)
  -- Natural number equality
  | natEq (v1 v2 : Nat) (h : v1 = v2)

mutual
  /--
  Values are the final result of the evaluation of well-typed expressions under a well-typed
  environment. We also assume here that the expressions and environment were "fully annotated",
  meaning all subexpressions have the correct `TypeInfo` field. The `TypeInfo` of the value
  is, by the type preservation property, the same as that of their expression under its environment.
  -/
  inductive Value
    -- Type universes. It is assumed `Univ` is reduced/simplified
    | sort : Univ → Value
    -- Values can only be an application if its a stuck application. That is, if
    -- the head of the application is neutral
    | app : Neutral → List SusValue → Value
    -- Lambdas are unevaluated expressions with environments for their free
    -- variables apart from their argument variables
    | lam : Name → BinderInfo → SusValue → Expr → Env → Value
    -- Pi types will have thunks for their domains and unevaluated expressions
    -- analogous to lambda bodies for their codomains
    | pi : Name → BinderInfo → SusValue → Expr → Env → Value
    | lit : Literal → Value
    | litProp : LiteralProp → Value
    -- An exception constructor is used to catch bugs in the evaluator/typechecker
    | exception : TypecheckError → Value
    deriving Inhabited

  /--
  Suspended values are thunks that return a value. For optimization purposes, the value's
  `TypeInfo`, which by type preservation comes from the underlying expression that gave
  rise to this value by means of evaluation, is saved outside the thunk, instead of in
  the values themselves. This allows us to extract it without needing to force the thunk.
  -/
  inductive SusValue
  | mk : TypeInfo → Thunk Value → SusValue

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
  inductive Env
    | mk : List SusValue → List Univ → Env
    deriving Inhabited

  /--
  A neutral term is either a variable or a constant with not enough arguments to
  reduce. They appear as the head of a stuck application.
  -/
  inductive Neutral
    | fvar  : Name → Nat → Neutral
    | const : Name → ConstIdx → List Univ → Neutral
    | proj  : Nat → SusValue → Neutral
    deriving Inhabited

end

/-- The arguments of a stuck sequence of applications `(h a1 ... an)` -/
abbrev Args := List SusValue

instance : Inhabited SusValue where
  default := .mk default {fn := default}

def SusValue.info : SusValue → TypeInfo
| .mk info _ => info

def SusValue.get : SusValue → Value
| .mk _ thunk => thunk.get

def Neutral.ctorName : Neutral → String
  | .fvar ..  => "fvar"
  | .const .. => "const"
  | .proj .. => "proj"

def Value.ctorName : Value → String
  | .sort ..  => "sort"
  | .app ..  => "app"
  | .lam ..  => "lam"
  | .pi  ..  => "pi"
  | .lit ..  => "lit"
  | .litProp ..  => "litProp"
  | .exception .. => "exception"

namespace Env
/-- Gets the list of expressions from a environment -/
def exprs : Env → List SusValue
  | .mk l _ => l

/-- Gets the list of universes from a environment -/
def univs : Env → List Univ
  | .mk _ l => l

/-- Stacks a new expression in the environment -/
def extendWith (env : Env) (thunk : SusValue) : Env :=
  .mk (thunk :: env.exprs) env.univs

/-- Sets a list of expressions to a environment -/
def withExprs (env : Env) (exprs : List SusValue) : Env :=
  .mk exprs env.univs

end Env

/-- Creates a new constant with a name, a constant index and an universe list -/
def mkConst (name : Name) (k : ConstIdx) (univs : List Univ) : Value :=
  .app (.const name k univs) []

/-- Creates a new variable as a thunk -/
def mkSusVar (info : TypeInfo) (name : Name) (idx : Nat) : SusValue :=
  .mk info (.mk fun _ => .app (.fvar name idx) [])

inductive PrimConstOp
  | natAdd | natMul | natPow | natDecEq  | natSucc
  deriving Ord

inductive PrimConst
  | nat 
  | decT 
  | decF 
  | natZero 
  | string
  | op : PrimConstOp → PrimConst
  deriving Ord

def PrimConstOp.numArgs : PrimConstOp → Nat
  | .natAdd | .natMul | .natPow | .natDecEq => 2 | .natSucc => 1

def PrimConstOp.reducible : PrimConstOp → Bool
  | .natAdd | .natMul | .natPow | .natDecEq => true | .natSucc => false

instance : ToString PrimConst where toString
| .nat      => "Nat"
| .decT     => "Decidable.isTrue"
| .decF     => "Decidable.isFalse"
| .natZero  => "Nat.zero"
| .string   => "String"
| .op .natAdd   => "Nat.add"
| .op .natMul   => "Nat.mul"
| .op .natPow   => "Nat.pow"
| .op .natDecEq => "Nat.decEq"
| .op .natSucc  => "Nat.succ"

end Yatima.Typechecker

namespace Yatima.Expr

end Yatima.Expr
