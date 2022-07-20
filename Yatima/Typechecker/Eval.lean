import Yatima.Typechecker.CheckM
import Yatima.Typechecker.Value

namespace Yatima.Typechecker

mutual

  partial def evalConst (name : Name) (const : Const) (univs : List Univ) : CheckM Value :=
    match const with
    | .theorem _ x =>
      eval x.value { exprs := [] , univs }
    | .definition _ x =>
      match x.safety with
      | .safe => eval x.value { exprs := [] , univs }
      | .partial => pure $ mkConst name const univs
      | .unsafe => throw .unsafeDefinition --panic! "Unsafe definition found"
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
          eval ctor.rhs {exprs, univs}
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
            eval rule.rhs {exprs, univs}
          -- Since we assume expressions are previously type checked, we know that this constructor
          -- must have an associated recursion rule
          | none => throw .hasNoRecursionRule --panic! "Constructor has no associated recursion rule. Implementation is broken."
        | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)

  partial def eval (term : Expr) (env : Env Value) : CheckM Value :=
    match term with
    | .app _ fnc arg => do
      let res ← eval arg env
      let arg_thunk := Thunk.mk (fun _ => res)
      match (← eval fnc env) with
      | Value.lam _ _ bod lam_env => eval bod (extEnv lam_env arg_thunk)
      | Value.app var@(Neutral.fvar ..) args => pure $ Value.app var (arg_thunk :: args)
      | Value.app (Neutral.const name k k_univs) args => applyConst name k k_univs arg_thunk args
      -- Since terms are well-typed we know that any other case is impossible
      | _ => throw .impossibleEvalCase 
    | .lam _ name info _ bod => pure $ Value.lam name info bod env
    | .var _ _ idx =>
      let thunk := List.get! env.exprs idx
      pure thunk.get
    | .const _ name k const_univs => evalConst name k (List.map (instBulkReduce env.univs) const_univs)
    | .letE _ _ _ val bod => do
      let res ← eval val env
      let thunk := Thunk.mk (fun _ => res)
      eval bod (extEnv env thunk)
    | .fix _ _ bod => do
      let res ← eval term env
      let thunk := Thunk.mk (fun _ => res)
      eval bod (extEnv env thunk)
    | .pi _ name info dom img => do
      let res ← eval dom env
      let dom' := Thunk.mk (fun _ => res)
      pure $ Value.pi name info dom' img env
    | .sort _ univ => pure $ Value.sort (instBulkReduce env.univs univ)
    | .lit _ lit => pure $ Value.lit lit
    | .lty _ lty => pure $ Value.lty lty
    | .proj _ idx expr => do
      match (← eval expr env) with
      | .app (.const _ (.constructor _ ctor) _) args =>
        -- Since terms are well-typed, we can be sure that this constructor is of a structure-like inductive
        -- and, furthermore, that the index is in range of `args`
        let idx := ctor.params + idx
        pure $ (List.get! args idx).get
      | .app neu args => pure $ .proj idx neu args
      | _ => throw .impossibleProjectioCase --panic! "Impossible case on projections"

end

end Yatima.Typechecker
