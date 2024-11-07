prelude
import yTypeChecker.Init

namespace Lean

inductive BinderInfo where
  /-- Default binder annotation, e.g. `(x : α)` -/
  | default
  /-- Implicit binder annotation, e.g., `{x : α}` -/
  | implicit
  /-- Strict implicit binder annotation, e.g., `{{ x : α }}` -/
  | strictImplicit
  /-- Local instance binder annotataion, e.g., `[Decidable α]` -/
  | instImplicit
  deriving Inhabited, BEq, Repr

/-- Literal values for `Expr`. -/
inductive Literal where
  /-- Natural number literal -/
  | natVal (val : Nat)
  /-- String literal -/
  | strVal (val : String)
  deriving Inhabited, BEq, Repr

inductive Expr where
  /--
  The `bvar` constructor represents bound variables, i.e. occurrences
  of a variable in the expression where there is a variable binder
  above it (i.e. introduced by a `lam`, `forallE`, or `letE`).

  The `deBruijnIndex` parameter is the *de-Bruijn* index for the bound
  variable. See [the Wikipedia page on de-Bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index)
  for additional information.

  For example, consider the expression `fun x : Nat => forall y : Nat, x = y`.
  The `x` and `y` variables in the equality expression are constructed
  using `bvar` and bound to the binders introduced by the earlier
  `lam` and `forallE` constructors. Here is the corresponding `Expr` representation
  for the same expression:
  ```lean
  .lam `x (.const `Nat [])
    (.forallE `y (.const `Nat [])
      (.app (.app (.app (.const `Eq [.succ .zero]) (.const `Nat [])) (.bvar 1)) (.bvar 0))
      .default)
    .default
  ```
  -/
  | bvar (deBruijnIndex : Nat)

  /--
  The `fvar` constructor represent free variables. These *free* variable
  occurrences are not bound by an earlier `lam`, `forallE`, or `letE`
  constructor and its binder exists in a local context only.

  Note that Lean uses the *locally nameless approach*. See [McBride and McKinna](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.365.2479&rep=rep1&type=pdf)
  for additional details.

  When "visiting" the body of a binding expression (i.e. `lam`, `forallE`, or `letE`),
  bound variables are converted into free variables using a unique identifier,
  and their user-facing name, type, value (for `LetE`), and binder annotation
  are stored in the `LocalContext`.
  -/
  | fvar (fvarId : FVarId)

  /--
  Metavariables are used to represent "holes" in expressions, and goals in the
  tactic framework. Metavariable declarations are stored in the `MetavarContext`.
  Metavariables are used during elaboration, and are not allowed in the kernel,
  or in the code generator.
  -/
  | mvar (mvarId : MVarId)

  /--
  Used for `Type u`, `Sort u`, and `Prop`:
  - `Prop` is represented as `.sort .zero`,
  - `Sort u` as ``.sort (.param `u)``, and
  - `Type u` as ``.sort (.succ (.param `u))``
  -/
  | sort (u : Level)

  /--
  A (universe polymorphic) constant that has been defined earlier in the module or
  by another imported module. For example, `@Eq.{1}` is represented
  as ``Expr.const `Eq [.succ .zero]``, and `@Array.map.{0, 0}` is represented
  as ``Expr.const `Array.map [.zero, .zero]``.
  -/
  | const (declName : Name) (us : List Level)

  /--
  A function application.

  For example, the natural number one, i.e. `Nat.succ Nat.zero` is represented as
  ``Expr.app (.const `Nat.succ []) (.const .zero [])``.
  Note that multiple arguments are represented using partial application.

  For example, the two argument application `f x y` is represented as
  `Expr.app (.app f x) y`.
  -/
  | app (fn : Expr) (arg : Expr)

  /--
  A lambda abstraction (aka anonymous functions). It introduces a new binder for
  variable `x` in scope for the lambda body.

  For example, the expression `fun x : Nat => x` is represented as
  ```
  Expr.lam `x (.const `Nat []) (.bvar 0) .default
  ```
  -/
  | lam (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo)

  /--
  A dependent arrow `(a : α) → β)` (aka forall-expression) where `β` may dependent
  on `a`. Note that this constructor is also used to represent non-dependent arrows
  where `β` does not depend on `a`.

  For example:
  - `forall x : Prop, x ∧ x`:
    ```lean
    Expr.forallE `x (.sort .zero)
      (.app (.app (.const `And []) (.bvar 0)) (.bvar 0)) .default
    ```
  - `Nat → Bool`:
    ```lean
    Expr.forallE `a (.const `Nat [])
      (.const `Bool []) .default
    ```
  -/
  | forallE (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo)

  /--
  Let-expressions.

  **IMPORTANT**: The `nonDep` flag is for "local" use only. That is, a module should not "trust" its value for any purpose.
  In the intended use-case, the compiler will set this flag, and be responsible for maintaining it.
  Other modules may not preserve its value while applying transformations.

  Given an environment, a metavariable context, and a local context,
  we say a let-expression `let x : t := v; e` is non-dependent when it is equivalent
  to `(fun x : t => e) v`. In contrast, the dependent let-expression
  `let n : Nat := 2; fun (a : Array Nat n) (b : Array Nat 2) => a = b` is type correct,
  but `(fun (n : Nat) (a : Array Nat n) (b : Array Nat 2) => a = b) 2` is not.

  The let-expression `let x : Nat := 2; Nat.succ x` is represented as
  ```
  Expr.letE `x (.const `Nat []) (.lit (.natVal 2)) (.app (.const `Nat.succ []) (.bvar 0)) true
  ```
  -/
  | letE (declName : Name) (type : Expr) (value : Expr) (body : Expr) (nonDep : Bool)

  /--
  Natural number and string literal values.

  They are not really needed, but provide a more compact representation in memory
  for these two kinds of literals, and are used to implement efficient reduction
  in the elaborator and kernel. The "raw" natural number `2` can be represented
  as `Expr.lit (.natVal 2)`. Note that, it is definitionally equal to:
  ```lean
  Expr.app (.const `Nat.succ []) (.app (.const `Nat.succ []) (.const `Nat.zero []))
  ```
  -/
  | lit : Literal → Expr

  /--
  Metadata (aka annotations).

  We use annotations to provide hints to the pretty-printer,
  store references to `Syntax` nodes, position information, and save information for
  elaboration procedures (e.g., we use the `inaccessible` annotation during elaboration to
  mark `Expr`s that correspond to inaccessible patterns).

  Note that `Expr.mdata data e` is definitionally equal to `e`.
  -/
  | mdata (data : MData) (expr : Expr)

  /--
  Projection-expressions. They are redundant, but are used to create more compact
  terms, speedup reduction, and implement eta for structures.
  The type of `struct` must be an structure-like inductive type. That is, it has only one
  constructor, is not recursive, and it is not an inductive predicate. The kernel and elaborators
  check whether the `typeName` matches the type of `struct`, and whether the (zero-based) index
  is valid (i.e., it is smaller than the number of constructor fields).
  When exporting Lean developments to other systems, `proj` can be replaced with `typeName`.`rec`
  applications.

  Example, given `a : Nat × Bool`, `a.1` is represented as
  ```
  .proj `Prod 0 a
  ```
  -/
  | proj (typeName : Name) (idx : Nat) (struct : Expr)
-- with
--   @[computed_field, extern "lean_expr_data"]
--   data : @& Expr → Data
--     | .const n lvls => mkData (mixHash 5 <| mixHash (hash n) (hash lvls)) 0 0 false false (lvls.any Level.hasMVar) (lvls.any Level.hasParam)
--     | .bvar idx => mkData (mixHash 7 <| hash idx) (idx+1)
--     | .sort lvl => mkData (mixHash 11 <| hash lvl) 0 0 false false lvl.hasMVar lvl.hasParam
--     | .fvar fvarId => mkData (mixHash 13 <| hash fvarId) 0 0 true
--     | .mvar fvarId => mkData (mixHash 17 <| hash fvarId) 0 0 false true
--     | .mdata _m e =>
--       let d := e.data.approxDepth.toUInt32+1
--       mkData (mixHash d.toUInt64 <| e.data.hash) e.data.looseBVarRange.toNat d e.data.hasFVar e.data.hasExprMVar e.data.hasLevelMVar e.data.hasLevelParam
--     | .proj s i e =>
--       let d := e.data.approxDepth.toUInt32+1
--       mkData (mixHash d.toUInt64 <| mixHash (hash s) <| mixHash (hash i) e.data.hash)
--           e.data.looseBVarRange.toNat d e.data.hasFVar e.data.hasExprMVar e.data.hasLevelMVar e.data.hasLevelParam
--     | .app f a => mkAppData f.data a.data
--     | .lam _ t b _ =>
--       let d := (max t.data.approxDepth.toUInt32 b.data.approxDepth.toUInt32) + 1
--       mkDataForBinder (mixHash d.toUInt64 <| mixHash t.data.hash b.data.hash)
--         (max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1))
--         d
--         (t.data.hasFVar || b.data.hasFVar)
--         (t.data.hasExprMVar || b.data.hasExprMVar)
--         (t.data.hasLevelMVar || b.data.hasLevelMVar)
--         (t.data.hasLevelParam || b.data.hasLevelParam)
--     | .forallE _ t b _ =>
--       let d := (max t.data.approxDepth.toUInt32 b.data.approxDepth.toUInt32) + 1
--       mkDataForBinder (mixHash d.toUInt64 <| mixHash t.data.hash b.data.hash)
--         (max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1))
--         d
--         (t.data.hasFVar || b.data.hasFVar)
--         (t.data.hasExprMVar || b.data.hasExprMVar)
--         (t.data.hasLevelMVar || b.data.hasLevelMVar)
--         (t.data.hasLevelParam || b.data.hasLevelParam)
--     | .letE _ t v b _ =>
--       let d := (max (max t.data.approxDepth.toUInt32 v.data.approxDepth.toUInt32) b.data.approxDepth.toUInt32) + 1
--       mkDataForLet (mixHash d.toUInt64 <| mixHash t.data.hash <| mixHash v.data.hash b.data.hash)
--         (max (max t.data.looseBVarRange.toNat v.data.looseBVarRange.toNat) (b.data.looseBVarRange.toNat - 1))
--         d
--         (t.data.hasFVar || v.data.hasFVar || b.data.hasFVar)
--         (t.data.hasExprMVar || v.data.hasExprMVar || b.data.hasExprMVar)
--         (t.data.hasLevelMVar || v.data.hasLevelMVar || b.data.hasLevelMVar)
--         (t.data.hasLevelParam || v.data.hasLevelParam || b.data.hasLevelParam)
--     | .lit l => mkData (mixHash 3 (hash l))
deriving Inhabited
