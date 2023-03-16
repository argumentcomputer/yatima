import Yatima.Typechecker.TypecheckM
import Yatima.Typechecker.Printing
import Yatima.Datatypes.Lurk
import Yatima.Common.ToLDON

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

open IR
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
def mkInductiveProjF (block : F) (idx : Nat) (quick : Bool) : F :=
  let indF : Const := .inductiveProj ⟨block, idx⟩
  if quick then .ofNat $ (Hashable.hash indF).toNat
  else indF.toLDON.commit default |>.1

/-- TODO document. This function is overwritten btw -/
def mkConstructorProjF (block : F) (idx : Nat) (cidx : Nat) (quick : Bool) : F :=
  let ctorF : Const := .constructorProj ⟨block, idx, cidx⟩
  if quick then .ofNat $ (Hashable.hash ctorF).toNat
  else ctorF.toLDON.commit default |>.1

/-- TODO document. This function is overwritten btw -/
def mkRecursorProjF (block : F) (idx : Nat) (ridx : Nat) (quick : Bool) : F :=
  let recrF : Const := .recursorProj ⟨block, idx, ridx⟩
  if quick then .ofNat $ (Hashable.hash recrF).toNat
  else recrF.toLDON.commit default |>.1

/-- TODO document. This function is overwritten btw -/
def mkDefinitionProjF (block : F) (idx : Nat) (quick : Bool) : F :=
  let defnF : Const := .definitionProj ⟨block, idx⟩
  if quick then .ofNat $ (Hashable.hash defnF).toNat
  else defnF.toLDON.commit default |>.1

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
  | none => throw s!"TypedConst for {f} not found"

end Typechecker

namespace IR

open Typechecker (TypecheckM derefConst)

def getIndFromProj : InductiveProj → TypecheckM Inductive
  | ⟨indBlockF, idx⟩ => do
    let .mutIndBlock inds := derefConst indBlockF (← read).store
      | throw "Invalid Const kind. Expected mutIndBlock"
    let some ind := inds.get? idx
      | throw s!"Mutual inductive block doesn't contain index {idx}"
    pure ind

def getDefFromProj : DefinitionProj → TypecheckM Definition
  | ⟨defBlockF, idx⟩ => do
    let .mutDefBlock defs := derefConst defBlockF (← read).store
      | throw "Invalid Const kind. Expected mutDefBlock"
    let some defn := defs.get? idx
      | throw s!"Mutual definition block doesn't contain index {idx}"
    pure defn

def getCtorFromProj : ConstructorProj → TypecheckM Constructor
  | ⟨indBlockF, idx, cidx⟩ => do
    let ind ← getIndFromProj ⟨indBlockF, idx⟩
    let some ctor := ind.ctors.get? cidx
      | throw s!"Inductive doesn't contain constructor with index {cidx}"
    pure ctor

def getRecrFromProj : RecursorProj → TypecheckM Recursor
  | ⟨indBlockF, idx, ridx⟩ => do
    let ind ← getIndFromProj ⟨indBlockF, idx⟩
    let some recr := ind.recrs.get? ridx
      | throw s!"Inductive doesn't contain recursor with index {ridx}"
    pure recr

namespace Const

def levels : Const → TypecheckM Nat
  | .axiom      x
  | .theorem    x
  | .opaque     x
  | .definition x
  | .quotient   x => pure x.lvls
  | .inductiveProj   p => do pure (← getIndFromProj  p).lvls
  | .constructorProj p => do pure (← getCtorFromProj p).lvls
  | .recursorProj    p => do pure (← getRecrFromProj p).lvls
  | .definitionProj  p => do pure (← getDefFromProj  p).lvls
  | _ => throw "Can't retrieve universe levels of mutual blocks"

def type : Const → TypecheckM Expr
  | .axiom      x
  | .theorem    x
  | .opaque     x
  | .definition x
  | .quotient   x => pure x.type
  | .inductiveProj   p => do pure (← getIndFromProj  p).type
  | .constructorProj p => do pure (← getCtorFromProj p).type
  | .recursorProj    p => do pure (← getRecrFromProj p).type
  | .definitionProj  p => do pure (← getDefFromProj  p).type
  | _ => throw "Can't retrieve type of mutual blocks"

end Const

end IR

namespace Typechecker

open PP

mutual
  /--
  Evaluates a `TypedExpr` into a `Value`.

  Evaluation here means applying functions to arguments, resuming evaluation of suspended thunks,
  evaluating a constant, instantiating a universe variable, evaluating the body of a let binding
  and evaluating a projection.
  -/
  partial def eval (t : TypedExpr) : TypecheckM Value := match t with
    | .app fnc arg => do
      let ctx ← read
      let argThunk := suspend arg ctx (← get)
      let fnc ← eval fnc
      apply fnc argThunk
    | .lam dom bod => do
      let ctx ← read
      let dom' := suspend dom ctx (← get)
      pure $ .lam dom' bod ctx.env
    | .var idx => do
      let some thunk := (← read).env.exprs.get? idx
        | throw s!"Index {idx} is out of range for expression environment"
      pure $ thunk.get
    | .const f const_univs => do
      let env := (← read).env
      let const_univs := const_univs.map (Univ.instBulkReduce env.univs)
      evalConst f const_univs
    | .letE _ val bod => do
      let thunk := suspend val (← read) (← get)
      withExtendedEnv thunk (eval bod)
    | .pi dom img => do
      let ctx ← read
      let dom' := suspend dom ctx (← get)
      pure $ .pi dom' img ctx.env
    | .sort univ => do
      let env := (← read).env
      pure $ .sort (Univ.instBulkReduce env.univs univ)
    | .lit lit =>
      pure $ .lit lit
    | .proj ind idx expr => do
      let val ← eval expr
      match val with
      | .app (.const f _) args =>
        match derefConst f (← read).store with
        | .constructorProj p =>
          let ctor ← getCtorFromProj p
          -- Since terms are well-typed, we can be sure that this constructor is of a structure-like inductive
          -- and, furthermore, that the index is in range of `args`
          let idx := ctor.params + idx
          let some arg := args.reverse.get? idx
            | throw s!"Invalid projection of index {idx} but constructor has only {args.length} arguments"
          pure $ arg.get
        | _ => pure $ .neu (.proj ind idx val)
      | .app .. => pure $ .neu (.proj ind idx val)
      | e => throw s!"Value {← ppValue e} is impossible to project"

  partial def evalConst' (f : F) (univs : List Univ) : TypecheckM Value := do
    match derefConst f (← read).store with
    | .theorem _
    | .definition _ =>
      match ← derefTypedConst f with
      | .theorem _ deref => withEnv ⟨[], univs⟩ $ eval deref
      | .definition _ deref part =>
        if part then pure $ mkConst f univs
        else withEnv ⟨[], univs⟩ $ eval deref
      | _ => throw "Invalid const kind for evaluation"
    | _ => pure $ mkConst f univs

  /-- Evaluates the `Yatima.Const` that's referenced by a constant index -/
  partial def evalConst (const : F) (univs : List Univ) : TypecheckM Value := do
    if ← primFWith .natZero (pure false) (pure $ · == const) then pure $ .lit (.natVal 0)
    else if (← fPrim const) matches .some (.op _) then pure $ mkConst const univs
    else evalConst' const univs

  /--
  Suspends the evaluation of a Yatima expression `expr : TypedExpr` in a particular `ctx : TypecheckCtx`

  Suspended evaluations can be resumed by evaluating `Thunk.get` on the resulting Thunk.
  -/
  partial def suspend (expr : TypedExpr) (ctx : TypecheckCtx) (stt : TypecheckState) : SusValue :=
    { fn := fun _ =>
      match TypecheckM.run ctx stt (eval expr) with
      | .ok a =>
        a
      | .error e => .exception e }

  /--
  Applies `value : Value` to the argument `arg : SusValue`.

  Applications are split into cases on whether `value` is a `Value.lam`, the application of a constant
  or the application of a free variable.

  * `Value.lam` : Descends into and evaluates the body of the lambda expression
  * `Value.app (.const ..)` : Applies the constant to the argument as expected using `applyConst`
  * `Value.app (.fvar ..)` : Returns an unevaluated `Value.app`
  -/
  partial def apply (val : Value) (arg : SusValue) : TypecheckM Value :=
    match val with
    | .lam _ bod lamEnv =>
      withNewExtendedEnv lamEnv arg (eval bod)
    | .app (.const f kUnivs) args => applyConst f kUnivs arg args
    | .app neu args => pure $ .app neu (arg :: args)
    -- Since terms are well-typed we know that any other case is impossible
    | _ => throw "Invalid case for apply"

  /--
  Applies a named constant, referred by its constant index `f : F` to the list of arguments
  `arg :: args`.

  The application of the constant is split into cases on whether it is an inductive recursor,
  a quotient, or any other constant (which returns an unreduced application)
   -/
  partial def applyConst (f : F) (univs : List Univ) (arg : SusValue) (args : List SusValue) : TypecheckM Value := do
    if let some $ .op p ← fPrim f then
      if args.length < p.numArgs - 1 then
        pure $ .app (.const f univs) (arg :: args)
      else
        let op := p.toPrimOp
        let argsArr := (Array.mk $ arg :: args).reverse
        match ← op.op $ argsArr with
        | .some v => pure v
        | .none =>
          if p.reducible then
            (arg :: args).foldrM (init := ← evalConst' f univs)
              fun arg acc => apply acc arg
          else pure $ .app (.const f univs) (arg :: args)

    -- Assumes a partial application of f to args, which means in particular,
    -- that it is in normal form
    else match ← derefTypedConst f with
    | .recursor _ params motives minors indices isK indProj rules =>
      let majorIdx := params + motives + minors + indices
      if args.length != majorIdx then
        pure $ .app (.const f univs) (arg :: args)
      else if isK then
        -- sanity check
        let nArgs := args.length
        let nDrop := params + motives + 1
        if nArgs < nDrop then
          throw s!"Too few arguments ({nArgs}). At least {nDrop} needed"
        let minorIdx := nArgs - nDrop
        let some minor := args.get? minorIdx | throw s!"Index {minorIdx} is out of range"
        pure minor.get
      else
        let params := args.take params
        match ← toCtorIfLitOrStruct indProj params univs arg with
        | .app (Neutral.const f _) args' => match ← derefTypedConst f with
          | .constructor _ idx _ =>
            match rules.get? idx with
            | some (fields, rhs) =>
              let exprs := (args'.take fields) ++ (args.drop indices)
              withEnv ⟨exprs, univs⟩ $ eval rhs.toImplicitLambda
            -- Since we assume expressions are previously type checked, we know that this constructor
            -- must have an associated recursion rule
            | none => throw s!"Constructor {f} has no associated recursion rule"
          | _ => pure $ .app (Neutral.const f univs) (arg :: args)
        | _ => pure $ .app (Neutral.const f univs) (arg :: args)
    | .quotient _ kind => match kind with
      | .lift => applyQuot arg args 6 1 (.app (.const f univs) (arg :: args))
      | .ind  => applyQuot arg args 5 0 (.app (.const f univs) (arg :: args))
      | _ => pure $ .app (.const f univs) (arg :: args)
    | _ => pure $ .app (.const f univs) (arg :: args)

  /--
  Applies a quotient to a value. It might reduce if enough arguments are applied to it
  -/
  partial def applyQuot (major? : SusValue) (args : List SusValue)
      (reduceSize argPos : Nat) (default : Value) : TypecheckM Value :=
    let argsLength := args.length + 1
    if argsLength == reduceSize then
      match major?.get with
      | .app (.const majorFn _) majorArgs => do
        match ← derefTypedConst majorFn with
        | .quotient _ .ctor =>
          -- Sanity check (`majorArgs` should have size 3 if the typechecking is correct)
          if majorArgs.length != 3 then throw "majorArgs should have size 3"
          let some majorArg := majorArgs.head? | throw "majorArgs can't be empty"
          let some head := args.get? argPos | throw s!"{argPos} is an invalid index for args"
          apply head.get majorArg
        | _ => pure default
      | _ => pure default
    else if argsLength < reduceSize then
      pure default
    else
      throw s!"argsLength {argsLength} can't be greater than reduceSize {reduceSize}"

  partial def toCtorIfLitOrStruct (indProj : InductiveProj) (params : List SusValue) (univs : List Univ) (thunk : SusValue) : TypecheckM Value :=
    match thunk.get with
    | .lit (.natVal v) => do
      let zeroIdx ← primF .natZero
      let succIdx ← primF (.op .natSucc)
      if v == 0 then pure $ mkConst zeroIdx []
      else
        let thunk : SusValue := Value.lit $ .natVal (v-1)
        pure $ .app (.const succIdx []) [thunk]
    | .lit (.strVal _) => throw "TODO Reduction of string"
    | e => do match indProj with
      | ⟨f, i⟩ =>
        let ind ← getIndFromProj indProj
        -- must be a struct to eta expand
        if !ind.struct then
          pure e
        else
          let quick := (← read).quick
          let ctorF := mkConstructorProjF f i 0 quick
          match e with
          | .app (.const f _) _ => if ctorF == f then
            -- already eta expanded
            return e
          | _ => pure ()
          let ctor ← match ind.ctors with
            | [ctor] => pure ctor
            | _ =>
              let f := mkInductiveProjF f i (← read).quick
              throw s!"{(← read).constNames.getF f} should be a struct with only one constructor"
          let etaExpand (e : Value) : TypecheckM Value := do
            let mut projArgs : List SusValue := params
            for idx in [:ctor.fields] do
              projArgs := projArgs ++ [.mk fun _ =>
                .neu (.proj (mkInductiveProjF f i quick) idx e)]
            let len := projArgs.length
            if h : len > 0 then
              let lastIdx := len.pred
              let lastArg := projArgs.get ⟨lastIdx, Nat.pred_lt' h⟩
              let annotatedArgs := projArgs.take lastIdx ++ [lastArg]
              pure $ .app (.const ctorF univs) annotatedArgs
            else
              pure $ .neu (.const ctorF univs)
          etaExpand e
end

mutual
  /--
  Quoting transforms a value into a (typed) expression. It is the right-inverse of evaluation:
  evaluating a quoted value results in the value itself.
  -/
  partial def quote (lvl : Nat) (env : Env) : Value → TypecheckM TypedExpr
    | .sort univ => pure $ .sort (univ.instBulkReduce env.univs)
    | .app neu args => do
      args.foldrM (init := ← quoteNeutral lvl env neu) fun arg acc => do
        pure $ .app acc $ ← quote lvl env arg.get
    | .lam dom bod env' => do
      let dom ← quote lvl env dom.get
      let var := mkSusVar lvl
      let bod ← quoteExpr (lvl+1) bod (env'.extendWith var)
      pure $ .lam dom bod
    | .pi dom img env' => do
      let dom ← quote lvl env dom.get
      let var := mkSusVar lvl
      let img ← quoteExpr (lvl+1) img (env'.extendWith var)
      pure $ .pi dom img
    | .lit lit => pure $ .lit lit
    | .exception e => throw e

  partial def quoteExpr (lvl : Nat) (expr : TypedExpr) (env : Env) : TypecheckM TypedExpr :=
    match expr with
    | .var idx => do
      match env.exprs.get? idx with
     | some val => quote lvl env val.get
     | none => throw s!"Unbound variable _@{idx}"
    | .app fnc arg => do
      let fnc ← quoteExpr lvl fnc env
      let arg ← quoteExpr lvl arg env
      pure $ .app fnc arg
    | .lam dom bod => do
      let dom ← quoteExpr lvl dom env
      let var := mkSusVar lvl
      let bod ← quoteExpr (lvl+1) bod (env.extendWith var)
      pure $ .lam dom bod
    | .letE typ val bod => do
      let typ ← quoteExpr lvl typ env
      let val ← quoteExpr lvl val env
      let var := mkSusVar lvl
      let bod ← quoteExpr (lvl+1) bod (env.extendWith var)
      pure $ .letE typ val bod
    | .pi dom img => do
      let dom ← quoteExpr lvl dom env
      let var := mkSusVar lvl
      let img ← quoteExpr (lvl+1) img (env.extendWith var)
      pure $ .pi dom img
    | .proj ind idx expr => do
      let expr ← quoteExpr lvl expr env
      pure $ .proj ind idx expr
    | .const idx univs => pure $ .const idx (univs.map (Univ.instBulkReduce env.univs))
    | .sort univ => pure $ .sort (univ.instBulkReduce env.univs)
    | .lit .. => pure expr

  partial def quoteNeutral (lvl : Nat) (env : Env) : Neutral → TypecheckM TypedExpr
    | .fvar  idx => pure $ .var (lvl - idx - 1)
    | .const cidx univs => pure $ .const cidx (univs.map (Univ.instBulkReduce env.univs))
    | .proj  f ind val => do
      pure $ .proj f ind (← quote lvl env val)
end

end Yatima.Typechecker
