import Yatima.Const

namespace Yatima.Typechecker

-- Expressions are things to be evaluated, given an appropriate environment.
-- Values are the result of evaluating (reducing, normalizing) expressions in an
-- environment. Finally, environments are maps that gives free variables of
-- expressions their values. When we talk about "unevaluated expressions",
-- you should think of these expression/environment pairs
structure Env (Value : Type) where
  -- The environment will bind free variables to different things, depending on
  -- the evaluation strategy.
  -- 1) Strict evaluation: binds free variables to values
  -- 2) Non-strict evaluation: binds free variables to unevaluated expressions
  -- 3) Lazy evaluation (i.e. non-strict without duplication of work): binds free variables to thunks
  -- Here we chose lazy evaluation since it is more efficient for typechecking.
  exprs : List (Thunk Value)
  -- Since we also have universes with free variables, we need to add an
  -- environment for universe variables as well:
  univs : List Univ

mutual
-- A neutral term is either a variable or a constant with not enough arguments to reduce.
-- They appear as the head of a stuck application.
inductive Neutral
-- Here variables also carry their types, but this is purely for an optimization
| fvar : Name → Nat → Thunk Value → Neutral
| const : Name → ConstIdx → List Univ → Neutral

-- Yatima values. We assume that values are only reduced from well-typed expressions.
inductive Value
-- Type universes. It is assumed `Univ` is reduced/simplified
| sort : Univ → Value
-- Values can only be an application if its a stuck application. That is, if
-- the head of the application is neutral
| app : Neutral → List (Thunk Value) → Value
--  Lambdas are unevaluated expressions with environments for their free
--  variables apart from their argument variables
| lam : Name → BinderInfo → Expr → Env Value → Value
--  Pi types will have thunks for their domains and unevaluated expressions
--  analogous to lambda bodies for their codomains
| pi : Name → BinderInfo → Thunk Value → Expr → Env Value → Value
| lit : Literal → Value
| lty : LitType → Value
| proj : Nat → Neutral → List (Thunk Value) → Value
deriving Inhabited
end

def Neutral.name : Neutral → Name
  | .fvar  n .. => n
  | .const n .. => n

-- The arguments of a stuck sequence of applications `(h a1 ... an)`
abbrev Args := List (Thunk Value)

instance : Inhabited (Thunk Value) where
  default := Thunk.mk (fun _ => Value.sort Univ.zero)

end Yatima.Typechecker
