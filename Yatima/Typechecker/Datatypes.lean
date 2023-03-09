import Yatima.Datatypes.Const
import YatimaStdLib.NonEmpty

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

/--
  The type info is a simplified form of the expression's type, with only relevant
  information for conversion checking, in order to get proof irrelevance and equality
  of unit-like values. Because of type preservation, a value will have the same info
  as the unevaluated expression inside the environment.

  - `unit` tells us that the expression's type is unit-like
  - `proof` tells us that the expression's type is a proposition (belong to `Prop`)
  - `sort` tells us that the expression's type itself is a `Sort u`

  When used in expressions, `sort`s can have uninstantiated and unreduced universes.
  When used in values, `sort`s will have only reduced and instantiated universes.
-/
inductive TypeInfo
  | unit | proof | prop | none
  | sort : Univ → TypeInfo
  deriving BEq, Inhabited, Repr

/--
  Auxiliary structure to add type info to values
-/
structure AddInfo (Body : Type) where
  info : TypeInfo
  body : Body
  deriving BEq, Inhabited

inductive Expr
  | var   : Nat → Expr
  | sort  : Univ → Expr
  -- NOTE: F here represents a hash of a normal `IR.Const`, as that is how we index into `TypecheckState.typedConsts`
  | const : F → List Univ → Expr
  | app   : AddInfo Expr → AddInfo Expr → Expr
  | lam   : AddInfo Expr → AddInfo Expr → Expr
  | pi    : AddInfo Expr → AddInfo Expr → Expr
  | letE  : AddInfo Expr → AddInfo Expr → AddInfo Expr → Expr
  | lit   : Literal → Expr
  | proj  : F → Nat → AddInfo Expr → Expr
  deriving BEq, Inhabited

/-- Typed expressions are expressions that have been processed by the typechecker -/
abbrev TypedExpr := AddInfo Expr

/--
Remove all binders from an expression, converting a lambda into
an "implicit lambda". This is useful for constructing the `rhs` of
recursor rules.
-/
def TypedExpr.toImplicitLambda : TypedExpr → TypedExpr
  | .mk _ (.lam _ body) => toImplicitLambda body
  | x => x

inductive TypedConst
  | «axiom»     : (type : TypedExpr) → TypedConst
  | «theorem»   : (type deref : TypedExpr) → TypedConst
  | «inductive» : (type : TypedExpr) → (struct : Bool) → TypedConst
  | «opaque»    : (type value : TypedExpr) → TypedConst
  | definition  : (type deref : TypedExpr) → (part : Bool) → TypedConst
  | constructor : (type : TypedExpr) → (idx fields : Nat) → TypedConst
  | recursor    : (type : TypedExpr) → (params motives minors indices : Nat) → (k : Bool) → (indProj : InductiveProj) → (rules : List (Nat × TypedExpr)) → TypedConst
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
  environment. The `TypeInfo` of the value is, by the type preservation property, the same as
  that of their expression under its environment.
  -/
  inductive Value
    /-- Type universes. It is assumed `Univ` is reduced/simplified -/
    | sort : Univ → Value
    /-- Neutrals are free variables, constants that cannot be reduced by itself,
        or stuck projections --/
    | neu : Neutral → Value
    /-- Values can only be an application if its a stuck application. That is, if
    the head of the application is neutral.
    For `Value.app neu [a_1, a_2, ... a_n]`,
    We also keep the info of the head for quoting -/
    | app : AddInfo Neutral → NEList (AddInfo (Thunk Value)) → Value
    /-- Lambdas are unevaluated expressions with environments for their free
    variables apart from their argument variables -/
    | lam : AddInfo (Thunk Value) → TypedExpr → Env' (AddInfo (Thunk Value)) → Value
    /-- Pi types will have thunks for their domains and unevaluated expressions
    analogous to lambda bodies for their codomains -/
    | pi : AddInfo (Thunk Value) → TypedExpr → Env' (AddInfo (Thunk Value)) → Value
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
    | proj  : F → Nat → AddInfo Value → Neutral
    deriving Inhabited

end

abbrev TypedValue := AddInfo Value

/--
Suspended values are thunks that return a value. For optimization purposes, the value's
`TypeInfo`, which by type preservation comes from the underlying expression that gave
rise to this value by means of evaluation, is saved outside the thunk, instead of in
the values themselves. This allows us to extract it without needing to force the thunk.
-/
abbrev SusValue := AddInfo (Thunk Value)

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
abbrev Args := NEList SusValue

instance : Inhabited SusValue where
  default := .mk default {fn := default}

-- Auxiliary functions
def SusValue.thunk (sus : SusValue) : Thunk Value := sus.body
def SusValue.get (sus : SusValue) : Value := sus.body.get
def TypedValue.value (val : TypedValue) : Value := val.body
def TypedValue.sus (val : TypedValue) : SusValue := ⟨val.info, val.body⟩

def Value.ctorName : Value → String
  | .sort      .. => "sort"
  | .app       .. => "app"
  | .neu       .. => "neu"
  | .lam       .. => "lam"
  | .pi        .. => "pi"
  | .lit       .. => "lit"
  | .exception .. => "exception"

def Neutral.ctorName : Neutral → String
  | .fvar  .. => "fvar"
  | .const .. => "const"
  | .proj  .. => "proj"

namespace Env
/-- Stacks a new expression in the environment -/
def extendWith (env : Env) (thunk : SusValue) : Env :=
  .mk (thunk :: env.exprs) env.univs

/-- Sets a list of expressions to a environment -/
def withExprs (env : Env) (exprs : List SusValue) : Env :=
  .mk exprs env.univs

end Env

/-- Creates a new constant with a name, a constant index and an universe list -/
def mkConst (f : F) (univs : List Univ) : Value :=
  .neu (.const f univs)

/-- Creates a new variable as a thunk -/
def mkSusVar (info : TypeInfo) (idx : Nat) : SusValue :=
  .mk info (.mk fun _ => .neu (.fvar idx))

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
