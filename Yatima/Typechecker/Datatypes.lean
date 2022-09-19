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

/--
  The value's metadata is a simplified form of the value's type, with only
  relevant information for typechecking. Namely, whether the value is a proof
  or value of some unit-like type, which means conversion checking can be
  shortcircuited, or whether the value is a proposition, which is used for
  checking if a projection is allowed or not
-/
structure Value.Meta where
  prop? : Bool
  proofOrUnit? : Bool
  deriving Inhabited

mutual
  /-- Values are the final result of reduced well-typed expressions -/
  inductive Value
    -- Type universes. It is assumed `Univ` is reduced/simplified
    | sort : Value.Meta → Univ → Value
    -- Values can only be an application if its a stuck application. That is, if
    -- the head of the application is neutral
    | app : Value.Meta → Neutral → List (Thunk Value) → Value
    -- Lambdas are unevaluated expressions with environments for their free
    -- variables apart from their argument variables
    | lam : Value.Meta → Name → BinderInfo → Expr → Env → Value
    -- Pi types will have thunks for their domains and unevaluated expressions
    -- analogous to lambda bodies for their codomains
    | pi : Value.Meta → Name → BinderInfo → Thunk Value → Expr → Env → Value
    | lit : Value.Meta → Literal → Value
    | exception : Value.Meta → TypecheckError → Value
    deriving Inhabited

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
    | fvar  : Name → Nat → Neutral
    | const : Name → ConstIdx → List Univ → Neutral
    | proj  : Nat → Value → Neutral
    deriving Inhabited

end

def Neutral.ctorName : Neutral → String
  | .fvar ..  => "fvar"
  | .const .. => "const"
  | .proj .. => "proj"

def Value.meta : Value → Value.Meta
  | .sort m ..
  | .app  m ..
  | .lam  m ..
  | .pi   m ..
  | .lit  m ..
  | .exception m .. => m

def Value.ctorName : Value → String
  | .sort ..  => "sort"
  | .app ..  => "app"
  | .lam ..  => "lam"
  | .pi  ..  => "pi"
  | .lit ..  => "lit"
  | .exception .. => "exception"

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
def mkConst (meta : Value.Meta) (name : Name) (k : ConstIdx) (univs : List Univ) : Value :=
  Value.app meta (Neutral.const name k univs) []

/-- Creates a new variable with a name, a de-Bruijn index and a type -/
def mkVar (meta : Value.Meta) (name : Name) (idx : Nat) : Value :=
  .app meta (Neutral.fvar name idx) []

/-- The arguments of a stuck sequence of applications `(h a1 ... an)` -/
abbrev Args := List (Thunk Value)

instance : Inhabited (Thunk Value) where
  default := {fn := default}

end Yatima.Typechecker

namespace Yatima.Expr

def Meta.toVal (m : Meta) : Typechecker.Value.Meta :=
  ⟨ m.prop?, m.proof? || m.unit? ⟩

end Yatima.Expr

