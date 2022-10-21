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

open TC

/--
Looks for a constant by its index `constIdx` in the `TypecheckCtx` store and
returns it if it is found. If the constant is not found it throws an error.

Note: The `name : Name` is used only in the error messaging
-/
def derefConst (name : Name) (constIdx : ConstIdx) : TypecheckM Const := do
  let consts := (← read).store.consts
  match consts.get? constIdx with
  | some const => pure const
  | none => throw $ .outOfConstsRange name constIdx consts.size

/--
Looks for a constant by its index `constIdx` in the `TypecheckState` cache of `TypedConst` and
returns it if it is found. If the constant is not found it throws an error.
Specifically, this function assumes that `checkConst name constIdx` has previously been called
(which populates this cache).

Note: The `name : Name` is used only in the error messaging
-/
def derefTypedConst (name : Name) (constIdx : ConstIdx) : TypecheckM TypedConst := do
  let tcConsts := (← get).tcConsts
  match tcConsts.get? constIdx with
  | some (some const) => pure const
  | some none => throw $ .missingTypedConst name constIdx
  | none => throw $ .outOfConstsRange name constIdx tcConsts.size

mutual
  /--
  Evaluates a `TypedExpr` into a `Value`.

  Evaluation here means applying functions to arguments, resuming evaluation of suspended thunks,
  evaluating a constant, instantiating a universe variable, evaluating the body of a let binding
  and evaluating a projection.
  -/
  partial def eval : TypedExpr → TypecheckM Value
    | .app _ fnc arg => do
      let ctx ← read
      let argThunk := suspend arg ctx (← get)
      let fnc ← eval fnc
      -- dbg_trace s!"evaluating {fnc}... {arg.info.struct?}"
      apply fnc argThunk
    | .lam _ name info dom bod => do
      let ctx ← read
      let dom' := suspend dom ctx (← get)
      pure $ .lam name info dom' bod ctx.env
    | .var _ name idx => do
      let exprs := (← read).env.exprs
      let some thunk := exprs.get? idx | throw $ .outOfRangeError name idx exprs.length
      pure $ thunk.get
    | .const _ name k const_univs => do
      let env := (← read).env
      evalConst name k (const_univs.map (Univ.instBulkReduce env.univs))
    | .letE _ _ _ val bod => do
      let thunk := suspend val (← read) (← get)
      withExtendedEnv thunk (eval bod)
    | .pi _ name info dom img => do
      let ctx ← read
      let dom' := suspend dom ctx (← get)
      pure $ .pi name info dom' img ctx.env
    | .sort _ univ => do
      let env := (← read).env
      pure $ .sort (Univ.instBulkReduce env.univs univ)
    | .lit _ lit =>
      pure $ .lit lit
    | .proj _ ind idx expr => do
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
        | _ => pure $ .app (.proj ind idx (.mk expr.info val)) []
      | .app .. => pure $ .app (.proj ind idx (.mk expr.info val)) []
      | e => throw $ .custom s!"Value {e} is impossible to project"

  partial def evalConst' (name : Name) (const : ConstIdx) (univs : List Univ) :
      TypecheckM Value := do
    match ← derefConst name const with
    | .theorem _
    | .definition _ =>
      match ← derefTypedConst name const with
      | .theorem _ deref => withEnv ⟨[], univs⟩ $ eval deref
      | .definition _ deref safety =>
        match safety with
        | .safe    => withEnv ⟨[], univs⟩ $ eval deref
        | .partial =>
          pure $ mkConst name const univs
        | .unsafe  => throw .unsafeDefinition
      | _ =>
        throw .impossible
    | _ =>
      pure $ mkConst name const univs

  /-- Evaluates the `Yatima.Const` that's referenced by a constant index -/
  partial def evalConst (name : Name) (const : ConstIdx) (univs : List Univ) :
      TypecheckM Value := do
    if (← primIndexWith .natZero (pure false) (pure $ · == const)) then pure $ .lit (.natVal 0)
    else if (← indexPrim const) matches .some (.op _) then pure $ mkConst name const univs
    else evalConst' name const univs

  /--
  Suspends the evaluation of a Yatima expression `expr : TypedExpr` in a particular `ctx : TypecheckCtx`

  Suspended evaluations can be resumed by evaluating `Thunk.get` on the resulting Thunk.
  -/
  partial def suspend (expr : TypedExpr) (ctx : TypecheckCtx) (stt : TypecheckState) : SusValue :=
    let thunk := { fn := fun _ =>
      match TypecheckM.run ctx stt (eval expr) with
      | .ok a => a
      | .error e => .exception e,
     }
    .mk expr.info thunk

  /--
  Applies `value : Value` to the argument `arg : SusValue`.

  Applications are split into cases on whether `value` is a `Value.lam`, the application of a constant
  or the application of a free variable.

  * `Value.lam` : Descends into and evaluates the body of the lambda expression
  * `Value.app (.const ..)` : Applies the constant to the argument as expected using `applyConst`
  * `Value.app (.fvar ..)` : Returns an unevaluated `Value.app`
  -/
  partial def apply (value : Value) (arg : SusValue) : TypecheckM Value :=
    match value with
    | .lam _ _ _ bod lamEnv =>
      withNewExtendedEnv lamEnv arg (eval bod)
    | .app (.const name k kUnivs) args => applyConst name k kUnivs arg args
    | .app var@(.fvar ..) args => pure $ .app var (arg :: args)
    | .app proj@(.proj ..) args => pure $ .app proj (arg :: args)
    -- Since terms are well-typed we know that any other case is impossible
    | _ => throw .impossible

  /--
  Applies a named constant, referred by its constant index `k : ConstIdx` to the list of arguments
  `arg :: args`.

  The application of the constant is split into cases on whether it is an inductive recursor,
  a quotient, or any other constant (which returns an unreduced application)
   -/
  partial def applyConst (name : Name) (k : ConstIdx) (univs : List Univ)
      (arg : SusValue) (args : Args) : TypecheckM Value := do

    if let some $ .op p ← indexPrim k then
      let newArgs := List.cons arg args
      if args.length < p.numArgs - 1 then
        pure $ .app (.const name k univs) $ newArgs
      else
        let op := p.toPrimOp
        let argsArr := (Array.mk newArgs).reverse
        match ← op.op argsArr with
        | .some v => pure v
        | .none => if p.reducible then
                     argsArr.foldlM (init := (← evalConst' name k univs)) fun acc arg => apply acc arg
                   else pure $ .app (.const name k univs) newArgs
    -- Assumes a partial application of k to args, which means in particular,
    -- that it is in normal form
    else match ← derefConst name k with
    | .intRecursor (.mk _ _ _ params motives minors indices isK) =>
      let majorIdx := params + motives + minors + indices
      if args.length != majorIdx then
        pure $ .app (Neutral.const name k univs) (arg :: args)
      else
        if isK then
          --dbg_trace s!"args: {args.map (·.get)} , {args.length}"
          --dbg_trace s!"{recur.params} , {recur.motives} , {recur.minors} , {recur.indices}"
          -- sanity check
          if args.length < (params + motives + 1) then
            throw .impossible
          let minorIdx := args.length - (params + motives + 1)
          let some minor := args.get? minorIdx | throw .impossible
          pure minor.get
        else
          match ← toCtorIfLit arg with
          | .app (Neutral.const kName k _) args' =>
            match ← derefConst kName k with
            | .constructor _ =>
              match ← derefTypedConst kName k with
              | .constructor _ rhs _ fields =>
                let exprs := (args'.take fields) ++ (args.drop indices)
                withEnv ⟨exprs, univs⟩ $ eval $ rhs.toImplicitLambda
              | _ => throw .impossible
            | _ => pure $ .app (Neutral.const name k univs) (arg :: args)
          | _ => pure $ .app (Neutral.const name k univs) (arg :: args)
    | .extRecursor _  =>
      match ← derefTypedConst name k with
      | .extRecursor _ params motives minors indices rules =>
        let majorIdx := params + motives + minors + indices
        if args.length != majorIdx then
          pure $ .app (Neutral.const name k univs) (arg :: args)
        else
          match ← toCtorIfLit arg with
          | .app (Neutral.const kName k _) args' => match ← derefConst kName k with
            | .constructor (.mk _ _ _ _ idx _ _ _) =>
              -- TODO: if rules are in order of indices, then we can use an array instead of a list for O(1) referencing
              match rules.find? (fun r => r.fst == idx) with
              | some (_, fields, rhs) =>
                let exprs := (args'.take fields) ++ (args.drop indices)
                withEnv ⟨exprs, univs⟩ $ eval rhs.toImplicitLambda
              -- Since we assume expressions are previously type checked, we know that this constructor
              -- must have an associated recursion rule
              | none => throw .hasNoRecursionRule --panic! "Constructor has no associated recursion rule. Implementation is broken."
            | _ => pure $ .app (Neutral.const name k univs) (arg :: args)
          | _ => pure $ .app (Neutral.const name k univs) (arg :: args)
      | _ => throw .impossible
    | .quotient (.mk _ _ _ kind) => match kind with
      | .lift => applyQuot arg args 6 1 $ .app (Neutral.const name k univs) (arg :: args)
      | .ind  => applyQuot arg args 5 0 $ .app (Neutral.const name k univs) (arg :: args)
      | _ => pure $ .app (Neutral.const name k univs) (arg :: args)
    | _ => pure $ .app (Neutral.const name k univs) (arg :: args)

  /--
  Applies a quotient to a value. It might reduce if enough arguments are applied to it
  -/
  partial def applyQuot (major? : SusValue) (args : Args)
      (reduceSize argPos : Nat) (default : Value) : TypecheckM Value :=
    let argsLength := args.length + 1
    if argsLength == reduceSize then
      match major?.get with
      | .app (.const name majorFn _) majorArgs => do
        match ← derefTypedConst name majorFn with
        | .quotient _ .ctor =>
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

  partial def toCtorIfLit : SusValue → TypecheckM Value
    | .mk info thunk => match thunk.get with
      | .lit (.natVal v) => do
        let zeroIdx ← primIndex .natZero
        let succIdx ← primIndex (.op .natSucc)
        if v == 0 then pure $ mkConst `Nat.Zero zeroIdx []
        else
          let thunk := SusValue.mk info (Value.lit (.natVal (v-1)))
          pure $ .app (.const `Nat.succ succIdx []) [thunk]
      | .lit (.strVal _) => throw $ .custom "TODO Reduction of string"
      | e => pure e
end

mutual
  /--
  Quoting transforms a value into a (typed) expression. It is the right-inverse of evaluation:
  evaluating a quoted value results in the value itself.
  -/
  partial def quote (lvl : Nat) (info : TypeInfo) : Value → TypecheckM TypedExpr
    | .sort univ => pure $ .sort info univ
    | .app neu args => do
      args.foldrM (init := ← quoteNeutral lvl neu) fun arg acc => do
      -- FIXME: replace `default` with proper info. I think we might have to add `TypeInfo` to the spine of arguments
        pure $ .app default acc $ ← quote lvl arg.info arg.get
    | .lam name binfo dom bod env => do
      let dom ← quote lvl dom.info dom.get
      -- NOTE: although we add a value with `default` as `TypeInfo`, this is overwritten by the info of the expression's value
      let var := mkSusVar default name lvl
      let bod ← quoteExpr (lvl+1) bod (env.extendWith var)
      pure $ .lam info name binfo dom bod
    | .pi name binfo dom img env => do
      let dom ← quote lvl dom.info dom.get
      let var := mkSusVar default name lvl
      let img ← quoteExpr (lvl+1) img (env.extendWith var)
      pure $ .pi info name binfo dom img
    | .lit lit => pure $ .lit info lit
    | .litProp _ => throw $ .custom "TODO"
    | .exception e => throw e

  partial def quoteExpr (lvl : Nat) (expr : TypedExpr) (env : Env) : TypecheckM TypedExpr :=
    match expr with
    | .var info name idx => do
      match env.exprs.get? idx with
      -- NOTE: if everything is correct, then `info` should coincide with `val.info`. We will choose `info` since
      -- this allows us to add values to the environment without knowing which `TypeInfo` it should take. See their
      -- previous note
     | some val => quote lvl info val.get
     | none => throw $ .custom s!"Unbound variable {name}"
    | .app info fnc arg => do
      let fnc ← quoteExpr lvl fnc env
      let arg ← quoteExpr lvl arg env
      pure $ .app info fnc arg
    | .lam info name bind dom bod => do
      let dom ← quoteExpr lvl dom env
      let var := mkSusVar default name lvl
      let bod ← quoteExpr (lvl+1) bod (env.extendWith var)
      pure $ .lam info name bind dom bod
    | .letE info name typ val bod => do
      let typ ← quoteExpr lvl typ env
      let val ← quoteExpr lvl val env
      let var := mkSusVar default name lvl
      let bod ← quoteExpr (lvl+1) bod (env.extendWith var)
      pure $ .letE info name typ val bod
    | .pi info name bind dom img => do
      let dom ← quoteExpr lvl dom env
      let var := mkSusVar default name lvl
      let img ← quoteExpr (lvl+1) img (env.extendWith var)
      pure $ .pi info name bind dom img
    | .proj info ind idx expr => do
      let expr ← quoteExpr lvl expr env
      pure $ .proj info ind idx expr
    | .const .. => pure expr
    | .sort .. => pure expr
    | .lit .. => pure expr

  partial def quoteNeutral (lvl : Nat) : Neutral → TypecheckM TypedExpr
    -- FIXME: replace `default` with proper info. I think we might have to add `TypeInfo` to `Neutral`
    | .fvar  nam idx => pure $ .var default nam (lvl - idx - 1)
    | .const nam cidx univs => pure $ .const default nam cidx univs
    | .proj  nam ind val => do
      pure $ .proj default nam ind (← quote lvl val.info val.value)
end
end Yatima.Typechecker
