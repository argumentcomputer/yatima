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
  The type info is a simplified form of the value's type, with only relevant
  information for conversion checking, in order to get proof irrelevance and equality
  of unit-like values.

  - `unit` tells us that the expression's type is unit-like
  - `proof` tells us that the expression's type is a proposition (belong to `Prop`)
  - `prop` tells us that the expression's type is `Prop` itself
-/
inductive TypeInfo
  | unit    : TypeInfo
  | proof   : TypeInfo
  | prop    : TypeInfo
  | none    : TypeInfo
  deriving BEq, Inhabited, Repr

/--
  A "suspended" version of `TypeInfo` with a `sort` enum that accepts a universe
  level pending instantiation. This is used in situations where we don't have enough
  information yet to know whether an expression should be tagged with `TypeInfo.prop`
  (i.e. Sort 0), for example in the types of universe-polymorphic constants.
-/
inductive SusTypeInfo
  | unit    : SusTypeInfo
  | proof   : SusTypeInfo
  | prop    : SusTypeInfo
  | sort    : Univ → SusTypeInfo
  | none    : SusTypeInfo
  deriving BEq, Inhabited, Repr

def TypeInfo.toSus : TypeInfo → SusTypeInfo
  | .unit    => .unit
  | .proof   => .proof
  | .prop    => .prop
  | .none    => .none

/-- Representation of expressions for evaluation -/
inductive TypedExpr
  | var   : SusTypeInfo → Name → Nat → TypedExpr
  | sort  : SusTypeInfo → Univ → TypedExpr
  | const : SusTypeInfo → Name → ConstIdx → List Univ → TypedExpr
  | app   : SusTypeInfo → TypedExpr → TypedExpr → TypedExpr
  | lam   : SusTypeInfo → Name → BinderInfo → TypedExpr → TypedExpr → TypedExpr
  | pi    : SusTypeInfo → Name → BinderInfo → TypedExpr → TypedExpr → TypedExpr
  | letE  : SusTypeInfo → Name → TypedExpr → TypedExpr → TypedExpr → TypedExpr
  | lit   : SusTypeInfo → Literal → TypedExpr
  | proj  : SusTypeInfo → ConstIdx → Nat → TypedExpr → TypedExpr
  deriving BEq, Inhabited, Repr

/--
Remove all binders from an expression, converting a lambda into
an "implicit lambda". This is useful for constructing the `rhs` of
recursor rules.
-/
def TypedExpr.toImplicitLambda : TypedExpr → TypedExpr
  | .lam _ _ _ _ body => toImplicitLambda body
  | x => x

inductive TypedConst
  | «axiom»     : (type : TypedExpr) → TypedConst
  | «theorem»   : (type deref : TypedExpr) → TypedConst
  | «inductive» : (type : TypedExpr) → (struct : Bool) → TypedConst
  | «opaque»    : (type value : TypedExpr) → TypedConst
  | definition  : (type deref : TypedExpr) → (safety : DefinitionSafety) → TypedConst
  | constructor : (type rhs : TypedExpr) → (idx fields : Nat) → TypedConst
  | extRecursor : (type : TypedExpr) → (params motives minors indices : Nat) → (rules : List (Nat × Nat × TypedExpr)) → TypedConst
  | intRecursor : (type : TypedExpr) → (params motives minors indices : Nat) → (k : Bool) → TypedConst
  | quotient    : (type : TypedExpr) → (kind : QuotKind) → TypedConst
  deriving Inhabited, BEq

def TypedConst.type : TypedConst → TypedExpr
  | «axiom»     type ..
  | «theorem»   type ..
  | «inductive» type ..
  | «opaque»    type ..
  | definition  type ..
  | constructor type ..
  | extRecursor type ..
  | intRecursor type ..
  | quotient    type .. => type

mutual
  /--
  Values are the final result of the evaluation of well-typed expressions under a well-typed
  environment. The `TypeInfo` of the value is, by the type preservation property, the same as
  that of their expression under its environment.
  -/
  inductive Value
    -- Type universes. It is assumed `Univ` is reduced/simplified
    | sort : Univ → Value
    -- Values can only be an application if its a stuck application. That is, if
    -- the head of the application is neutral.
    -- For `Value.app neu [(a_1, ti_1), (a_2, ti_2), ... (a_n, ti_n)]`,
    -- `ti_i` representst the `TypeInfo` of the partial application thus far (`neu a_1 a_2 ... a_i`);
    -- this preserves information necessary to implement the quoting (i.e. read-back)
    -- functionality that is used in lambda inference
    | app : Neutral → List (SusValue × TypeInfo) → Value
    -- Lambdas are unevaluated expressions with environments for their free
    -- variables apart from their argument variables
    | lam : Name → BinderInfo → SusValue → TypedExpr → Env → Value
    -- Pi types will have thunks for their domains and unevaluated expressions
    -- analogous to lambda bodies for their codomains
    | pi : Name → BinderInfo → SusValue → TypedExpr → Env → Value
    | lit : Literal → Value
    -- An exception constructor is used to catch bugs in the evaluator/typechecker
    | exception : TypecheckError → Value
    deriving Inhabited

  inductive TypedValue
    | mk : TypeInfo → Value → TypedValue

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
    | proj  : Nat → ConstIdx → TypedValue → Neutral
    deriving Inhabited

end

/-- The arguments of a stuck sequence of applications `(h a1 ... an)` -/
abbrev Args := List (SusValue × TypeInfo)

instance : Coe Args (List SusValue) where
  coe := fun args => args.map (·.1)

instance : Inhabited SusValue where
  default := .mk default {fn := default}

def TypedExpr.info : TypedExpr → SusTypeInfo
| var   info ..
| sort  info ..
| const info ..
| app   info ..
| lam   info ..
| pi    info ..
| letE  info ..
| lit   info ..
| proj  info .. => info

def SusValue.info : SusValue → TypeInfo
| .mk info _ => info

def SusValue.thunk : SusValue → Thunk Value
| .mk _ thunk => thunk

def SusValue.get : SusValue → Value
| .mk _ thunk => thunk.get

def TypedValue.info : TypedValue → TypeInfo
| .mk info _ => info

def TypedValue.value : TypedValue → Value
| .mk _ val => val

def TypedValue.sus : TypedValue → SusValue
| .mk info val => .mk info val

def Value.ctorName : Value → String
  | .sort ..  => "sort"
  | .app ..  => "app"
  | .lam ..  => "lam"
  | .pi  ..  => "pi"
  | .lit ..  => "lit"
  | .exception .. => "exception"

def Neutral.ctorName : Neutral → String
  | .fvar ..  => "fvar"
  | .const .. => "const"
  | .proj .. => "proj"

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
| .nat      => "Nat"
| .bool     => "Bool"
| .boolTrue     => "Bool.true"
| .boolFalse     => "Bool.false"
| .natZero  => "Nat.zero"
| .string   => "String"
| .op .natAdd   => "Nat.add"
| .op .natMul   => "Nat.mul"
| .op .natPow   => "Nat.pow"
| .op .natBeq => "Nat.beq"
| .op .natBle => "Nat.ble"
| .op .natBlt => "Nat.blt"
| .op .natSucc  => "Nat.succ"

end Yatima.Typechecker
