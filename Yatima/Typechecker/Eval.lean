import Yatima.Typechecker.TypecheckM

namespace Yatima.Typechecker

def mkConst (name : Name) (k : ConstIdx) (univs : List Univ) : Value :=
  Value.app (Neutral.const name k univs) []

def getConst! (constIdx : ConstIdx) : TypecheckM Const := do
  let env ← read
  match env.store.get? constIdx with
  | some const => pure const
  | none => throw .outOfDefnRange

mutual
  partial def suspend (expr : Expr) (ctx : Context) : Thunk Value :=
    Thunk.mk (fun _ => TypecheckM.run! ctx "Panic in eval. Implementation broken" (eval expr))

  partial def eval : Expr → TypecheckM Value
    | .app fnc arg => do
      let ctx ← read
      let arg_thunk := suspend arg ctx
      apply (← eval fnc) arg_thunk
    | .lam name info _ bod => do
       let env := (← read).env
       pure $ Value.lam name info bod env
    | .var _ idx => do
      let env := (← read).env
      let thunk := List.get! env.exprs idx
      pure thunk.get
    | .const name k const_univs => do
      let env := (← read).env
      evalConst name k (const_univs.map (instBulkReduce env.univs))
    | .letE _ _ val bod => do
      let thunk := suspend val (← read)
      extEnv thunk (eval bod)
    | .pi name info dom img => do
      let ctx ← read
      let dom' := suspend dom ctx
      pure $ Value.pi name info dom' img ctx.env
    | .sort univ => do
      let env := (← read).env
      pure $ Value.sort (instBulkReduce env.univs univ)
    | .lit lit => pure $ Value.lit lit
    | .lty lty => pure $ Value.lty lty
    | .proj idx expr => do
      match (← eval expr) with
      | .app neu@(.const _ ctor _) args => match (← read).store.get! ctor with
        | .constructor ctor =>
          -- Since terms are well-typed, we can be sure that this constructor is of a structure-like inductive
          -- and, furthermore, that the index is in range of `args`
          let idx := ctor.params + idx
          pure $ (List.get! args idx).get
        | _ => pure $ .proj idx neu args
      | .app neu args => pure $ .proj idx neu args
      | _ => throw .impossible

  partial def evalConst (name : Name) (const : ConstIdx) (univs : List Univ) :
      TypecheckM Value := do
    match (← read).store.get! const with
    | .theorem x => withEnv ⟨[], univs⟩ $ eval x.value
    | .definition x =>
      match x.safety with
      | .safe => eval x.value
      | .partial => pure $ mkConst name const univs
      | .unsafe => throw .unsafeDefinition
    | _ => pure $ mkConst name const univs

  partial def apply (value : Value) (arg : Thunk Value) : TypecheckM Value :=
    match value with
    | .lam _ _ bod lam_env => withExtEnv lam_env arg (eval bod)
    | .app (.const name k k_univs) args' => applyConst name k k_univs arg args'
    | .app var@(.fvar ..) args' => pure $ Value.app var (arg :: args')
    -- Since terms are well-typed we know that any other case is impossible
    | _ => throw .impossible

  partial def applyConst (name : Name) (k : ConstIdx) (univs : List Univ) (arg : Thunk Value) (args : Args) : TypecheckM Value := do
    -- Assumes a partial application of k to args, which means in particular, that it is in normal form
    match (← read).store.get! k with
    | .intRecursor recur =>
      let major_idx := recur.params + recur.motives + recur.minors + recur.indices
      if args.length != major_idx then pure $ Value.app (Neutral.const name k univs) (arg :: args)
      else
        match arg.get with
        | .app (Neutral.const _ ctor _) args' => match (← read).store.get! ctor with
          | .constructor ctor =>
            let exprs := List.append (List.take ctor.fields args') (List.drop recur.indices args)
            withEnv ⟨exprs, univs⟩ $ eval ctor.rhs
          | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
        | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | .extRecursor recur =>
      let major_idx := recur.params + recur.motives + recur.minors + recur.indices
      if args.length != major_idx then pure $ Value.app (Neutral.const name k univs) (arg :: args)
      else
        match arg.get with
        | .app (Neutral.const _ ctor _) args' => match (← read).store.get! ctor with
          | .constructor ctor =>
            -- TODO: if rules are in order of indices, then we can use an array instead of a list for O(1) referencing
            match List.find? (fun r => r.ctor.idx == ctor.idx) recur.rules with
            | some rule =>
              let exprs := List.append (List.take rule.fields args') (List.drop recur.indices args)
              withEnv ⟨exprs, univs⟩ $ eval rule.rhs
            -- Since we assume expressions are previously type checked, we know that this constructor
            -- must have an associated recursion rule
            | none => throw .hasNoRecursionRule
          | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
        | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | .quotient quotVal => match quotVal.kind with
      | .lift => reduceQuot arg args 6 1 $ Value.app (Neutral.const name k univs) (arg :: args)
      | .ind  => reduceQuot arg args 5 0 $ Value.app (Neutral.const name k univs) (arg :: args)
      | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)

  partial def suspend (expr : Expr) (ctx : Context) : Thunk Value :=
    Thunk.mk (fun _ =>
      match TypecheckM.run ctx (eval expr) with
      | .ok a => a
      | .error e => .exception e )

  partial def eval : Expr → TypecheckM Value
    | .app fnc arg => do
      let ctx ← read
      let arg_thunk := suspend arg ctx
      match (← eval fnc) with
      | .lam _ _ bod lam_env => withExtEnv lam_env arg_thunk (eval bod)
      | .app var@(.fvar ..) args => pure $ Value.app var (arg_thunk :: args)
      | .app (.const name k k_univs) args => applyConst name k k_univs arg_thunk args
      -- Since terms are well-typed we know that any other case is impossible
      | _ => throw .impossibleEvalCase
    | .lam name info _ bod => do
       let env := (← read).env
       pure $ Value.lam name info bod env
    | .var _ idx => do
      let env := (← read).env
      let thunk := List.get! env.exprs idx
      pure thunk.get
    | .const name k const_univs => do
      let env := (← read).env
      evalConst name k (const_univs.map (instBulkReduce env.univs))
    | .letE _ _ val bod => do
      let thunk := suspend val (← read)
      extEnv thunk (eval bod)
    | .pi name info dom img => do
      let ctx ← read
      let dom' := suspend dom ctx
      pure $ Value.pi name info dom' img ctx.env
    | .sort univ => do
      let env := (← read).env
      pure $ Value.sort (instBulkReduce env.univs univ)
    | .lit lit => pure $ Value.lit lit
    | .lty lty => pure $ Value.lty lty
    | .proj idx expr => do
      match (← eval expr) with
      | .app neu@(.const _ ctor _) args => match (← read).store.get! ctor with
        | .constructor ctor =>
          -- Since terms are well-typed, we can be sure that this constructor is of a structure-like inductive
          -- and, furthermore, that the index is in range of `args`
          let idx := ctor.params + idx
          pure $ (List.get! args idx).get
        | _ => pure $ .proj idx neu args
      | .app neu args => pure $ .proj idx neu args
      | _ => throw .impossibleProjectionCase

end

end Yatima.Typechecker
