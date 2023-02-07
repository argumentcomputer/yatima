import Yatima.Typechecker.TypecheckM
import Yatima.Typechecker.Printing
import Yatima.Commit.ToLDON
import Yatima.Datatypes.Lurk

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

namespace Yatima

open TC
open Lurk (F)

namespace Typechecker

/--
Looks for a constant by its hash `f : F` in a store and
returns it if found. Panics otherwise.

In the code generator, this function has to be overwritten with `(open f)`,
ignoring the second argument.
-/
def derefConst (f : F) (store : Store) : Const :=
  store.find! f

/-- TODO document. This function is overwritten btw -/
def mkConstructorProjF (block : F) (idx : Nat) (cidx : Nat) : F :=
  let ctorF : Const := .constructorProj ⟨block, idx, cidx⟩
  let (ctorF, _) := ctorF.toLDON.commit default
  ctorF

/--
Looks for a constant by its hash `f : F` in the `TypecheckState` cache of `TypedConst` and
returns it if it is found. If the constant is not found it throws an error.
Specifically, this function assumes that `checkConst name f` has previously been called
(which populates this cache).

Note: The `name : Name` is used only in the error messaging
-/
def derefTypedConst (f : F) : TypecheckM TypedConst := do
  match (← get).typedConsts.find? f with
  | some const => pure const
  | none => throw $ .custom "TODO"

end Typechecker

namespace TC.Const

open Typechecker (TypecheckM derefConst)

def levels : Const → TypecheckM Nat
  | .axiom      x
  | .theorem    x
  | .opaque     x
  | .definition x
  | .quotient   x => pure x.lvls
  | .inductiveProj ⟨f, i⟩ => do match derefConst f (← read).store with
    | .mutIndBlock inds => match inds.get? i with
      | .some ind => pure ind.lvls
      | _ => throw sorry
    | _ => throw sorry
  | .constructorProj ⟨f, i, ci⟩ => do match derefConst f (← read).store with
    | .mutIndBlock inds => match inds.get? i with
      | .some ind => match ind.ctors.get? ci with
        | .some ctor => pure ctor.lvls
        | _ => throw sorry
      | _ => throw sorry
    | _ => throw sorry
  | .recursorProj ⟨f, i, ri⟩ => do match derefConst f (← read).store with
    | .mutIndBlock inds => match inds.get? i with
      | .some ind => match ind.recrs.get? i with
        | .some recr => pure recr.lvls
        | _ => throw sorry
      | _ => throw sorry
    | _ => throw sorry
  | .definitionProj ⟨f, i⟩ => do match derefConst f (← read).store with
    | .mutDefBlock defs => match defs.get? i with
      | .some defn => pure defn.lvls
      | _ => throw sorry
    | _ => throw sorry
  | _ => throw sorry

def type : Const → TypecheckM Expr
  | .axiom      x
  | .theorem    x
  | .opaque     x
  | .definition x
  | .quotient   x => pure x.type
  | .inductiveProj ⟨f, i⟩ => do match derefConst f (← read).store with
    | .mutIndBlock inds => match inds.get? i with
      | .some ind => pure ind.type
      | _ => throw sorry
    | _ => throw sorry
  | .constructorProj ⟨f, i, ci⟩ => do match derefConst f (← read).store with
    | .mutIndBlock inds => match inds.get? i with
      | .some ind => match ind.ctors.get? ci with
        | .some ctor => pure ctor.type
        | _ => throw sorry
      | _ => throw sorry
    | _ => throw sorry
  | .recursorProj ⟨f, i, ri⟩ => do match derefConst f (← read).store with
    | .mutIndBlock inds => match inds.get? i with
      | .some ind => match ind.recrs.get? ri with
        | .some recr => pure recr.type
        | _ => throw sorry
      | _ => throw sorry
    | _ => throw sorry
  | .definitionProj ⟨f, i⟩ => do match derefConst f (← read).store with
    | .mutDefBlock defs => match defs.get? i with
      | .some defn => pure defn.type
      | _ => throw sorry
    | _ => throw sorry
  | _ => throw sorry

end TC.Const

namespace Typechecker

mutual
  /--
  Evaluates a `TypedExpr` into a `Value`.

  Evaluation here means applying functions to arguments, resuming evaluation of suspended thunks,
  evaluating a constant, instantiating a universe variable, evaluating the body of a let binding
  and evaluating a projection.
  -/
  partial def eval : TypedExpr → TypecheckM Value
    | .app i fnc arg => do
      let ctx ← read
      let argThunk := suspend arg ctx (← get)
      let fnc ← eval fnc
      apply fnc argThunk (i.update ctx.env.univs)
    | .lam _ dom bod => do
      let ctx ← read
      let dom' := suspend dom ctx (← get)
      pure $ .lam dom' bod ctx.env
    | .var _ idx => do
      let exprs := (← read).env.exprs
      let some thunk := exprs.get? idx | throw $ .outOfRangeError "TODO" idx exprs.length
      pure $ thunk.get
    | .const _ f const_univs => do
      let env := (← read).env
      evalConst f (const_univs.map (Univ.instBulkReduce env.univs))
    | .letE _ _ val bod => do
      let thunk := suspend val (← read) (← get)
      withExtendedEnv thunk (eval bod)
    | .pi _ dom img => do
      let ctx ← read
      let dom' := suspend dom ctx (← get)
      pure $ .pi dom' img ctx.env
    | .sort _ univ => do
      let env := (← read).env
      pure $ .sort (Univ.instBulkReduce env.univs univ)
    | .lit _ lit =>
      pure $ .lit lit
    | .proj _ ind idx expr => do
      let val ← eval expr
      match val with
      | .app (.const f _) args =>
        match derefConst f (← read).store with
        | .constructorProj ⟨f, i, ci⟩ =>
          let .mutIndBlock inds := derefConst f (← read).store | throw sorry
          let some ind := inds.get? i | throw sorry
          let some ctor := ind.ctors.get? ci | throw sorry
          -- Since terms are well-typed, we can be sure that this constructor is of a structure-like inductive
          -- and, furthermore, that the index is in range of `args`
          let idx := ctor.params + idx
          let some arg := args.reverse.get? idx
            | throw $ .custom s!"Invalid projection of index {idx} but constructor has only {args.length} arguments"
          pure $ arg.1.get
        | _ => pure $ .app (.proj ind idx (.mk (expr.info.update (← read).env.univs) val)) []
      | .app .. => pure $ .app (.proj ind idx (.mk (expr.info.update (← read).env.univs) val)) []
      | e => throw $ .custom s!"Value {e} is impossible to project"

  partial def evalConst' (f : F) (univs : List Univ) : TypecheckM Value := do
    match derefConst f (← read).store with
    | .theorem _
    | .definition _ =>
      match ← derefTypedConst f with
      | .theorem _ deref => withEnv ⟨[], univs⟩ $ eval deref
      | .definition _ deref safety =>
        match safety with
        | .safe    => withEnv ⟨[], univs⟩ $ eval deref
        | .partial => pure $ mkConst f univs
        | .unsafe  => throw .unsafeDefinition
      | _ => throw .impossible
    | _ => pure $ mkConst f univs

  /-- Evaluates the `Yatima.Const` that's referenced by a constant index -/
  partial def evalConst (const : F) (univs : List Univ) : TypecheckM Value := do
    if ← primFWith .natZero (pure false) (pure $ · == const) then pure $ .lit (.natVal 0)
    else if (← fPrim const) matches .some (.op _) then pure $ mkConst const univs
    else evalConst' const univs

  partial def SusTypeInfo.update (univs : List Univ) : SusTypeInfo → TypeInfo
  | .sort lvl => match lvl.instBulkReduce univs with
    | .zero => .prop
    | _ => .none
  | .unit  => .unit
  | .proof => .proof
  | .prop  => .prop
  | .none  => .none

  /--
  Suspends the evaluation of a Yatima expression `expr : TypedExpr` in a particular `ctx : TypecheckCtx`

  Suspended evaluations can be resumed by evaluating `Thunk.get` on the resulting Thunk.
  -/
  partial def suspend (expr : TypedExpr) (ctx : TypecheckCtx) (stt : TypecheckState) : SusValue :=
    let thunk := { fn := fun _ =>
      match TypecheckM.run ctx stt (eval expr) with
      | .ok a => a
      | .error e => .exception e }
    .mk (expr.info.update ctx.env.univs) thunk

  /--
  Applies `value : Value` to the argument `arg : SusValue`.

  Applications are split into cases on whether `value` is a `Value.lam`, the application of a constant
  or the application of a free variable.

  * `Value.lam` : Descends into and evaluates the body of the lambda expression
  * `Value.app (.const ..)` : Applies the constant to the argument as expected using `applyConst`
  * `Value.app (.fvar ..)` : Returns an unevaluated `Value.app`
  -/
  partial def apply (value : Value) (arg : SusValue) (i : TypeInfo) : TypecheckM Value :=
    match value with
    | .lam _ bod lamEnv =>
      withNewExtendedEnv lamEnv arg (eval bod)
    | .app (.const f kUnivs) args => applyConst f kUnivs arg args i
    | .app var@(.fvar ..) args => pure $ .app var ((arg, i) :: args)
    | .app proj@(.proj ..) args => pure $ .app proj ((arg, i) :: args)
    -- Since terms are well-typed we know that any other case is impossible
    | _ => throw .impossible

  /--
  Applies a named constant, referred by its constant index `f : F` to the list of arguments
  `arg :: args`.

  The application of the constant is split into cases on whether it is an inductive recursor,
  a quotient, or any other constant (which returns an unreduced application)
   -/
  partial def applyConst (f : F) (univs : List Univ)
      (arg : SusValue) (args : Args) (info : TypeInfo) : TypecheckM Value := do
    if let some $ .op p ← fPrim f then
      let newArgs := args.cons (arg, info)
      if args.length < p.numArgs - 1 then
        pure $ .app (.const f univs) $ newArgs
      else
        let op := p.toPrimOp
        let argsArr := (Array.mk newArgs).reverse
        match ← op.op $ argsArr.map (·.1) with
        | .some v => pure v
        | .none =>
          if p.reducible then
            argsArr.foldlM (init := ← evalConst' f univs)
              fun acc (arg, info) => apply acc arg info
          else pure $ .app (.const f univs) newArgs
    -- Assumes a partial application of f to args, which means in particular,
    -- that it is in normal form
    else match ← derefTypedConst f with
    | .recursor _ params motives minors indices isK indF rules =>
      let majorIdx := params + motives + minors + indices
      if args.length != majorIdx then
        pure $ .app (Neutral.const f univs) ((arg, info) :: args)
      else if isK then
        -- sanity check
        if args.length < (params + motives + 1) then
          throw .impossible
        let minorIdx := args.length - (params + motives + 1)
        let some minor := args.get? minorIdx | throw .impossible
        pure minor.1.get
      else
        let params := args.take params
        match ← toCtorIfLitOrStruct indF (params.map (·.1)) univs arg with
        | .app (Neutral.const f _) args' => match ← derefTypedConst f with
          | .constructor _ idx _ =>
            -- TODO: if rules are in order of indices, then we can use an array instead of a list for O(1) referencing
            match rules.get? idx with
            | some (fields, rhs) =>
              let exprs := (args'.take fields) ++ (args.drop indices)
              withEnv ⟨exprs, univs⟩ $ eval rhs.toImplicitLambda
            -- Since we assume expressions are previously type checked, we know that this constructor
            -- must have an associated recursion rule
            | none => throw .hasNoRecursionRule --panic! "Constructor has no associated recursion rule. Implementation is broken."
          | _ => pure $ .app (Neutral.const f univs) ((arg, info) :: args)
        | _ => pure $ .app (Neutral.const f univs) ((arg, info) :: args)
    | .quotient _ kind => match kind with
      | .lift => applyQuot arg args 6 1 (.app (Neutral.const f univs) ((arg, info) :: args)) info
      | .ind  => applyQuot arg args 5 0 (.app (Neutral.const f univs) ((arg, info) :: args)) info
      | _ => pure $ .app (Neutral.const f univs) ((arg, info) :: args)
    | _ => pure $ .app (Neutral.const f univs) ((arg, info) :: args)

  /--
  Applies a quotient to a value. It might reduce if enough arguments are applied to it
  -/
  partial def applyQuot (major? : SusValue) (args : Args)
      (reduceSize argPos : Nat) (default : Value) (info : TypeInfo) : TypecheckM Value :=
    let argsLength := args.length + 1
    if argsLength == reduceSize then
      match major?.get with
      | .app (.const majorFn _) majorArgs => do
        match ← derefTypedConst majorFn with
        | .quotient _ .ctor =>
          -- Sanity check (`majorArgs` should have size 3 if the typechecking is correct)
          if majorArgs.length != 3 then throw .impossible
          let some majorArg := majorArgs.head? | throw .impossible
          let some head := args.get? argPos | throw .impossible
          apply head.1.get majorArg.1 info
        | _ => pure default
      | _ => pure default
    else if argsLength < reduceSize then
      pure default
    else
      throw .impossible

  partial def toCtorIfLitOrStruct (indF : F) (params : List SusValue) (univs : List Univ) : SusValue → TypecheckM Value
    | .mk info thunk => match thunk.get with
      | .lit (.natVal v) => do
        let zeroIdx ← primF .natZero
        let succIdx ← primF (.op .natSucc)
        if v == 0 then pure $ mkConst zeroIdx []
        else
          let thunk := SusValue.mk info (Value.lit (.natVal (v-1)))
          pure $ .app (.const succIdx []) [(thunk, .none)]
      | .lit (.strVal _) => throw $ .custom "TODO Reduction of string"
      | e => do match derefConst indF (← read).store with
        | .inductiveProj ⟨f, i⟩ =>
          let .mutIndBlock inds := derefConst f (← read).store | throw sorry
          let some ind := inds.get? i | throw sorry
        -- | .inductive (.mk (struct := struct) (ctors := ctors) ..) =>
          if ind.struct then
            let ctor ← match ind.ctors with
              | [ctor] => pure ctor
              | _ => throw .impossible
            let ctorF := mkConstructorProjF f i 0
            let etaExpand (e : Value) : TypecheckM Value := do
              let mut projArgs : List SusValue := params
              for idx in [:ctor.fields] do
                -- FIXME get the correct TypeInfo for the projection
                projArgs := projArgs ++ [.mk .none $ .mk fun _ => .app (.proj indF idx $ .mk info e) []]
              let mut annotatedArgs := []
              if projArgs.length > 0 then do
                let some lastArg := projArgs.get? (projArgs.length - 1) | throw .impossible
                annotatedArgs := projArgs.take (projArgs.length - 1) |>.map (·, .none)
                annotatedArgs := annotatedArgs ++ [(lastArg, info)]
              pure $ .app (.const ctorF univs) $ annotatedArgs
            match e with
            | .app (.const f _) _ =>
              --dbg_trace s!"constant head: {n}, {idx}, {ctorIdx}"
              -- FIXME do not `etaExpand` if the struct is in `Prop`
              if ctorF == f then
                --dbg_trace s!"not eta-expanding..."
                -- this is already a constructor application
                pure e
              else 
                --dbg_trace s!"eta-expanding..."
                etaExpand e
            | _ => etaExpand e
          else
            pure e
        | _ => throw .impossible
end

mutual
  /--
  Quoting transforms a value into a (typed) expression. It is the right-inverse of evaluation:
  evaluating a quoted value results in the value itself.
  -/
  partial def quote (lvl : Nat) (info : SusTypeInfo) (env : Env) : Value → TypecheckM TypedExpr
    | .sort univ => pure $ .sort info (univ.instBulkReduce env.univs)
    | .app neu args => do
      args.foldrM (init := ← quoteNeutral lvl env neu) fun arg acc => do
        pure $ .app arg.2.toSus acc $ ← quote lvl arg.1.info.toSus env arg.1.get
    | .lam dom bod env' => do
      let dom ← quote lvl dom.info.toSus env dom.get
      -- NOTE: although we add a value with `default` as `TypeInfo`, this is overwritten by the info of the expression's value
      let var := mkSusVar default lvl
      let bod ← quoteExpr (lvl+1) bod (env'.extendWith var)
      pure $ .lam info dom bod
    | .pi dom img env' => do
      let dom ← quote lvl dom.info.toSus env dom.get
      let var := mkSusVar default lvl
      let img ← quoteExpr (lvl+1) img (env'.extendWith var)
      pure $ .pi info dom img
    | .lit lit => pure $ .lit info lit
    | .exception e => throw e

  partial def quoteExpr (lvl : Nat) (expr : TypedExpr) (env : Env) : TypecheckM TypedExpr :=
    match expr with
    | .var info idx => do
      match env.exprs.get? idx with
      -- NOTE: if everything is correct, then `info` should coincide with `val.info`. We will choose `info` since
      -- this allows us to add values to the environment without knowing which `TypeInfo` it should take. See their
      -- previous note
     | some val => quote lvl info env val.get
     | none => throw $ .custom s!"Unbound variable _@{idx}"
    | .app info fnc arg => do
      let fnc ← quoteExpr lvl fnc env
      let arg ← quoteExpr lvl arg env
      pure $ .app info fnc arg
    | .lam info dom bod => do
      let dom ← quoteExpr lvl dom env
      let var := mkSusVar default lvl
      let bod ← quoteExpr (lvl+1) bod (env.extendWith var)
      pure $ .lam info dom bod
    | .letE info typ val bod => do
      let typ ← quoteExpr lvl typ env
      let val ← quoteExpr lvl val env
      let var := mkSusVar default lvl
      let bod ← quoteExpr (lvl+1) bod (env.extendWith var)
      pure $ .letE info typ val bod
    | .pi info dom img => do
      let dom ← quoteExpr lvl dom env
      let var := mkSusVar default lvl
      let img ← quoteExpr (lvl+1) img (env.extendWith var)
      pure $ .pi info dom img
    | .proj info ind idx expr => do
      let expr ← quoteExpr lvl expr env
      pure $ .proj info ind idx expr
    | .const info idx univs => pure $ .const info idx (univs.map (Univ.instBulkReduce env.univs))
    | .sort info univ => pure $ .sort info (univ.instBulkReduce env.univs)
    | .lit .. => pure expr

  partial def quoteNeutral (lvl : Nat) (env : Env) : Neutral → TypecheckM TypedExpr
    -- FIXME: replace `default` with proper info. I think we might have to add `TypeInfo` to `Neutral`
    | .fvar  idx => pure $ .var default (lvl - idx - 1)
    | .const cidx univs => pure $ .const default cidx (univs.map (Univ.instBulkReduce env.univs))
    | .proj  f ind val => do
      pure $ .proj default f ind (← quote lvl val.info.toSus env val.value)
end
end Typechecker
end Yatima
