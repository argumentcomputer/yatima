import Yatima.Datatypes.Const
import Yatima.Typechecker.TypecheckError

namespace Yatima.Typechecker

/--
  Wrapper for `Thunk` with a representation string; useful for debugging.
-/
structure Thunk (α : Type u) extends Thunk α : Type u where
  repr : String := "[THUNKED]"

instance : Coe α $ Thunk α where
  coe a := {fn := fun _ => a}

instance [ToString α] : Coe α $ Thunk α where
  coe a := {fn := fun _ => a, repr := toString a}

/-!
# Basic concepts

* Expressions are objects to be evaluated given an appropriate environment
* Values are the result of evaluating (reducing, normalizing) expressions in a
environment
* Finally, environments map free variables of expressions to values

When we talk about "unevaluated expressions", you should think of these
expression/environment pairs. They are also called *closures*
-/

mutual

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
    | mk : List (Thunk Value) → List Univ → Env
    deriving Inhabited

  /--
  A neutral term is either a variable or a constant with not enough arguments to
  reduce. They appear as the head of a stuck application.
  -/
  inductive Neutral
    -- Here variables also carry their types purely for an optimization
    | fvar  : Name → Nat → Thunk Value → Neutral
    | const : Name → ConstIdx → List Univ → Neutral
    deriving Inhabited

  /-- Values are the final result of reduced well-typed expressions -/
  inductive Value
    -- Type universes. It is assumed `Univ` is reduced/simplified
    | sort : Univ → Value
    -- Values can only be an application if its a stuck application. That is, if
    -- the head of the application is neutral
    | app : Neutral → List (Thunk Value) → Value
    -- Lambdas are unevaluated expressions with environments for their free
    -- variables apart from their argument variables
    | lam : Name → BinderInfo → Expr → Env → Value
    -- Pi types will have thunks for their domains and unevaluated expressions
    -- analogous to lambda bodies for their codomains
    | pi : Name → BinderInfo → Thunk Value → Expr → Env → Value
    | lit : Literal → Value
    | proj : Nat → Neutral → List (Thunk Value) → Value
    | exception : TypecheckError → Value
    deriving Inhabited

end

def Neutral.ctorName : Neutral → String
  | .fvar ..  => "fvar"
  | .const .. => "const"

def Value.ctorName : Value → String
  | .sort _  => "sort"
  | .app ..  => "app"
  | .lam ..  => "lam"
  | .pi  ..  => "pi"
  | .lit  _  => "lit"
  | .proj .. => "proj"
  | .exception _ => "exception"

namespace Env

/-- Gets the list of expressions from a environment -/
def exprs : Env → List (Thunk Value)
  | .mk l _ => l

/-- Gets the list of universes from a environment -/
def univs : Env → List Univ
  | .mk _ l => l

/-- Stacks a new expression in the environment -/
def extendWith (env : Env) (thunk : Thunk Value) : Env :=
  .mk (thunk :: env.exprs) env.univs

/-- Sets a list of expressions to a environment -/
def withExprs (env : Env) (exprs : List (Thunk Value)) : Env :=
  .mk exprs env.univs

end Env

/-- Creates a new constant with a name, a constant index and an universe list -/
def mkConst (name : Name) (k : ConstIdx) (univs : List Univ) : Value :=
  Value.app (Neutral.const name k univs) []

/-- Creates a new variable with a name, a de-Bruijn index and a type -/
def mkVar (name : Name) (idx : Nat) (type : Thunk Value) : Value :=
  .app (Neutral.fvar name idx type) []

/-- The arguments of a stuck sequence of applications `(h a1 ... an)` -/
abbrev Args := List (Thunk Value)

instance : Inhabited (Thunk Value) where
  default := {fn := default}

end Yatima.Typechecker
