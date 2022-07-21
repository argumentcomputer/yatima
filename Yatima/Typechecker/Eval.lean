import Yatima.Typechecker.CheckM
import Yatima.Typechecker.Value

namespace Yatima.Typechecker

mutual

  partial def evalConst (name : Name) (const : Const) (univs : List Univ) : CheckM Value :=
    match const with
    | .theorem _ x => withEnv [] univs $ eval x.value
    | .definition _ x =>
      match x.safety with
      | .safe => eval x.value
      | .partial => pure $ mkConst name const univs
      | .unsafe => throw .unsafeDefinition
    | _ => pure $ mkConst name const univs

  partial def applyConst (name : Name) (k : Const) (univs : List Univ) (arg : Thunk Value) (args : Args) : CheckM Value :=
  -- Assumes a partial application of k to args, which means in particular, that it is in normal form
    match k with
    | .intRecursor _ recur =>
      let major_idx := recur.params + recur.motives + recur.minors + recur.indices
      if args.length != major_idx then pure $ Value.app (Neutral.const name k univs) (arg :: args)
      else
        match arg.get with
        | .app (Neutral.const _ (.constructor _ ctor) _) args' =>
          let exprs := List.append (List.take ctor.fields args') (List.drop recur.indices args)
          withEnv exprs univs $ eval ctor.rhs
        | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | .extRecursor _ recur =>
      let major_idx := recur.params + recur.motives + recur.minors + recur.indices
      if args.length != major_idx then pure $ Value.app (Neutral.const name k univs) (arg :: args)
      else
        match arg.get with
        | .app (Neutral.const _ (.constructor hash _) _) args' =>
          match List.find? (fun r => r.ctor == hash) recur.rules with
          | some rule =>
            let exprs := List.append (List.take rule.fields args') (List.drop recur.indices args)
            withEnv exprs univs $ eval rule.rhs
          -- Since we assume expressions are previously type checked, we know that this constructor
          -- must have an associated recursion rule
          | none => throw .hasNoRecursionRule --panic! "Constructor has no associated recursion rule. Implementation is broken."
        | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)

  partial def eval (term : Expr) : CheckM Value :=
    match term with
    | .app _ fnc arg => do
      let env := (← read).env
      let res ← eval arg
      let arg_thunk := Thunk.mk (fun _ => res)
      match (← eval fnc) with
      | Value.lam _ _ bod _ => extEnvHelper arg_thunk (eval bod)
      | Value.app var@(Neutral.fvar ..) args => pure $ Value.app var (arg_thunk :: args)
      | Value.app (Neutral.const name k k_univs) args => applyConst name k k_univs arg_thunk args
      -- Since terms are well-typed we know that any other case is impossible
      | _ => throw .impossibleEvalCase 
    | .lam _ name info _ bod => do
       let env := (← read).env
       pure $ Value.lam name info bod env
    | .var _ _ idx => do
      let env := (← read).env
      let thunk := List.get! env.exprs idx
      pure thunk.get
    | .const _ name k const_univs => do
      let env := (← read).env
      evalConst name k (List.map (instBulkReduce env.univs) const_univs)
    | .letE _ _ _ val bod => do
      let res ← eval val
      let thunk := Thunk.mk (fun _ => res)
      extEnvHelper thunk (eval bod)
    | .fix _ _ bod => do
      let res ← eval term
      let thunk := Thunk.mk (fun _ => res)
      extEnvHelper thunk (eval bod)
    | .pi _ name info dom img => do
      let env := (← read).env
      let res ← eval dom
      let dom' := Thunk.mk (fun _ => res)
      pure $ Value.pi name info dom' img env
    | .sort _ univ => do
      let env := (← read).env
      pure $ Value.sort (instBulkReduce env.univs univ)
    | .lit _ lit => pure $ Value.lit lit
    | .lty _ lty => pure $ Value.lty lty
    | .proj _ idx expr => do
      match (← eval expr) with
      | .app (.const _ (.constructor _ ctor) _) args =>
        -- Since terms are well-typed, we can be sure that this constructor is of a structure-like inductive
        -- and, furthermore, that the index is in range of `args`
        let idx := ctor.params + idx
        pure $ (List.get! args idx).get
      | .app neu args => pure $ .proj idx neu args
      | _ => throw .impossibleProjectionCase --panic! "Impossible case on projections"

end

end Yatima.Typechecker
