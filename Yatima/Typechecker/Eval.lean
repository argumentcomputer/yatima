import Yatima.Typechecker.TypecheckM
import Yatima.Typechecker.Printing

/-!
# Yatima typechecker: Eval

## Basic Structure

This is the first of the three main files that constitute the Yatima typechecker: `Eval`, `Equal`,
and `Infer`.

TODO: Add a high level overview of Eval in the context of Eval-Equal-Infer.

## Evaluate

In this module the evaluation (↔ reduction) of Yatima expressions is defined. Expressions that can
be reduced take a few forms, for example `.app fnc args`, constants, and suspdended evaluations.
Functions that can not be reduced further evaluate to unreduced Values or suspended thunks waiting
to evaluate further.
-/

namespace Yatima.Typechecker

/--
Looks for a constant by its index `constIdx` in the `TypecheckCtx` store and
returns it if it is found. If the constant is not found it throws an error.

Note: The `name : Name` is used only in the error messaging
-/
def derefConst (name : Name) (constIdx : ConstIdx) : TypecheckM Const := do
  let consts := (← read).pStore.consts
  match consts.get? constIdx with
  | some const => pure const
  | none => throw $ .outOfConstsRange name constIdx consts.size

mutual
  /--
  Evaluates a `Yatima.Expr` into a `Typechecker.Value`.

  Evaluation here means applying functions to arguments, resuming evaluation of suspended Thunks,
  evaluating a constant, instantiating a universe variable, evaluating the body of a let binding
  and evaluating a projection.
  -/
  partial def eval : Expr → TypecheckM Value
    | .app _ fnc arg => do
      let ctx ← read
      let argThunk := suspend arg ctx
      let fnc := (← eval fnc)
      apply fnc argThunk
    | .lam _ name info _ bod => do
      let env := (← read).env
      pure $ Value.lam name info bod env
    | .var _ name idx => do
      let exprs := (← read).env.exprs
      let some thunk := exprs.get? idx | throw $ .outOfRangeError name idx exprs.length
      pure thunk.get
    | .const _ name k const_univs => do
      let env := (← read).env
      evalConst name k (const_univs.map (Univ.instBulkReduce env.univs))
    | .letE _ _ _ val bod => do
      let thunk := suspend val (← read)
      withExtendedEnv thunk (eval bod)
    | .pi _ name info dom img => do
      let ctx ← read
      let dom' := suspend dom ctx
      pure $ Value.pi name info dom' img ctx.env
    | .sort _ univ => do
      let env := (← read).env
      pure $ Value.sort (Univ.instBulkReduce env.univs univ)
    | .lit _ lit => pure $ Value.lit lit
    | .proj _ idx expr => do
      let val ← eval expr
      match val with
      | .app (.const name k _) args =>
        match ← derefConst name k with
        | .constructor ctor =>
          -- Since terms are well-typed, we can be sure that this constructor is of a structure-like inductive
          -- and, furthermore, that the index is in range of `args`
          let idx := ctor.params + idx
          let some arg := args.reverse.get? idx
            | throw $ .custom s!"Invalid projection of index {idx} but constructor has only {args.length} arguments"
          pure $ arg.get
        | _ =>
          pure $ .app (.proj idx val) []
      | .app (.fvar ..) ..
      | .app (.proj ..) .. =>
        pure $ .app (.proj idx val) []
      | e => throw $ .custom s!"Value {e} is impossible to project"

  /-- Evaluates the `Yatima.Const` that's referenced by a constant index -/
  partial def evalConst (name : Name) (const : ConstIdx) (univs : List Univ) :
      TypecheckM Value := do
    let zero? ← zeroIndexWith (pure false) (fun zeroIdx => pure $ const == zeroIdx)
    if zero? then pure $ .lit (.natVal 0)
    else match ← derefConst name const with
    | .theorem x => withEnv ⟨[], univs⟩ $ eval x.value
    | .definition x =>
      match x.safety with
      | .safe    => withEnv ⟨[], univs⟩ $ eval x.value
      | .partial => pure $ mkConst name const univs
      | .unsafe  => throw .unsafeDefinition
    | _ => pure $ mkConst name const univs

  /--
  Suspends the evaluation of a Yatima expression `expr : Expr` in a particular `ctx : TypecheckCtx`

  Suspended evaluations can be resumed by evaluating `Thunk.get` on the resulting Thunk.
  -/
  partial def suspend (expr : Expr) (ctx : TypecheckCtx) : Thunk Value :=
    {fn := fun _ =>
      match TypecheckM.run ctx (eval expr) with
      | .ok a => a
      | .error e => .exception e,
     repr := toString expr}

  /--
  Applies `value : Value` to the argument `arg : Thunk Value`.

  Applications are split into cases on whether `value` is a `Value.lam`, the application of a constant
  or the application of a free variable.

  * `Value.lam` : Descends into and evaluates the body of the lambda expression
  * `Value.app (.const ..)` : Applies the constant to the argument as expected using `applyConst`
  * `Value.app (.fvar ..)` : Returns an unevaluated `Value.app`
  -/
  partial def apply (value : Value) (arg : Thunk Value) : TypecheckM Value :=
    match value with
    -- bod : fun y => x^1 + y^0
    | .lam _ _ bod lamEnv =>
      withNewExtendedEnv lamEnv arg (eval bod)
    | .app (.const name k kUnivs) args => applyConst name k kUnivs arg args
    | .app var@(.fvar ..) args => pure $ Value.app var (arg :: args)
    -- Since terms are well-typed we know that any other case is impossible
    | _ => throw .impossible

  /--
  Applies a named constant, referred by its constant index `k : ConstIdx` to the list of arguments
  `arg :: args`.

  The application of the constant is split into cases on whether it is an inductive recursor,
  a quotient, or any other constant (which returns an unreduced application)
   -/
  partial def applyConst (name : Name) (k : ConstIdx) (univs : List Univ)
      (arg : Thunk Value) (args : Args) : TypecheckM Value := do

    let succ? ← succIndexWith (pure false) (fun succIdx => pure $ k == succIdx)
    if succ? then
      -- Sanity check
      if !args.isEmpty then throw $ .custom "args should be empty"
      else match arg.get with
      | .lit (.natVal v) => pure $ .lit (.natVal (v+1))
      | _ => pure $ .app (.const name k univs) [arg]

    -- Assumes a partial application of k to args, which means in particular,
    -- that it is in normal form
    else match ← derefConst name k with
    | .intRecursor recur =>
      let majorIdx := recur.params + recur.motives + recur.minors + recur.indices
      if args.length != majorIdx then
       pure $ Value.app (Neutral.const name k univs) (arg :: args)
      else
        let arg ← toCtorIfLit arg.get
        match arg with
        | .app (Neutral.const kName k _) args' => match ← derefConst kName k with
          | .constructor ctor =>
            let exprs := (args'.take ctor.fields) ++ (args.drop recur.indices)
            withEnv ⟨exprs, univs⟩ $ eval ctor.rhs
          | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
        | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | .extRecursor recur =>
      let majorIdx := recur.params + recur.motives + recur.minors + recur.indices
      if args.length != majorIdx then
        pure $ Value.app (Neutral.const name k univs) (arg :: args)
      else
        let arg ← toCtorIfLit arg.get
        match arg with
        | .app (Neutral.const kName k _) args' => match ← derefConst kName k with
          | .constructor ctor =>
            -- TODO: if rules are in order of indices, then we can use an array instead of a list for O(1) referencing
            match recur.rules.find? (fun r => r.ctor.idx == ctor.idx) with
            | some rule =>
              let exprs := (args'.take rule.fields) ++ (args.drop recur.indices)
              withEnv ⟨exprs, univs⟩ $ eval rule.rhs
            -- Since we assume expressions are previously type checked, we know that this constructor
            -- must have an associated recursion rule
            | none => throw .hasNoRecursionRule --panic! "Constructor has no associated recursion rule. Implementation is broken."
          | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
        | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | .quotient quotVal => match quotVal.kind with
      | .lift => applyQuot arg args 6 1 $ Value.app (Neutral.const name k univs) (arg :: args)
      | .ind  => applyQuot arg args 5 0 $ Value.app (Neutral.const name k univs) (arg :: args)
      | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)

  /--
  Applies a quotient to a value. It might reduce if enough arguments are applied to it
  -/
  partial def applyQuot (major? : Thunk Value) (args : Args)
      (reduceSize argPos : Nat) (default : Value) : TypecheckM Value :=
    let argsLength := args.length + 1
    if argsLength == reduceSize then
      match major?.get with
      | .app (.const name majorFn _) majorArgs => do
        match ← derefConst name majorFn with
        | Const.quotient {kind := .ctor, ..} =>
          -- Sanity check (`majorArgs` should have size 3 if the typechecking is correct)
          if majorArgs.length != 3 then throw .impossible
          let some majorArg := majorArgs.head? | throw .impossible
          let some head := args.get? argPos | throw .impossible
          apply head.get majorArg
        | _ => pure default
      | _ => pure default
    else if argsLength < reduceSize then
      pure default
    else
      throw .impossible

  partial def toCtorIfLit : Value → TypecheckM Value
    | .lit (.natVal v) => do
      let zeroIdx ← zeroIndexWith (throw $ .custom "Cannot find definition of `Nat.Zero`") pure
      let succIdx ← succIndexWith (throw $ .custom "Cannot find definition of `Nat.Succ`") pure
      if v == 0 then evalConst `Nat.Zero zeroIdx []
      else pure $ .app (.const `Nat.succ succIdx []) [Value.lit (.natVal (v-1))]
    | .lit (.strVal _) => throw $ .custom "TODO Reduction of string"
    | e => pure e
end

end Yatima.Typechecker
