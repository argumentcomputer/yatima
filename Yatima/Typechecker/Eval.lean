import Yatima.Typechecker.Value

namespace Yatima.Typechecker

def mkConst (name : Name) (k : Const) (univs : List Univ) : Value :=
  Value.app (Neutral.const name k univs) []

def extEnv (env : Env Value) (thunk : Thunk Value) : Env Value :=
  {env with exprs := thunk :: env.exprs}

mutual
partial def evalConst (name : Name) (const : Const) (univs : List Univ) : Value :=
  match const with
  | .«theorem» _ x =>
    eval x.value { exprs := [] , univs }
  | .definition _ x =>
    match x.safety with
    | .safe => eval x.value { exprs := [] , univs }
    | .«partial» => mkConst name const univs
    | .«unsafe» => panic! "Unsafe definition found"
  | _ => mkConst name const univs

  partial def applyConst (name : Name) (k : Const) (univs : List Univ) (arg : Thunk Value) (args : Args) : Value :=
  -- Assumes a partial application of k to args, which means in particular, that it is in normal form
    match k with
    | .recursor _ recur =>
      let major_idx := recur.params + recur.motives + recur.minors + recur.indices
      if args.length != major_idx then Value.app (Neutral.const name k univs) (arg :: args)
      else
        match arg.get with
        | .app (Neutral.const _ (.constructor hash ctor) _) args' =>
          match List.find? (fun r => r.ctor == hash) recur.rules with
          | some rule =>
            let exprs := List.append (List.take rule.fields args') (List.drop recur.indices args)
            eval rule.rhs {exprs, univs}
          -- Since we assume expressions are previously type checked, we know that this constructor
          -- must have an associated recursion rule
          | none => panic! "Constructor has no associated recursion rule. Implementation is broken."
        | _ => Value.app (Neutral.const name k univs) (arg :: args)
    | _ => Value.app (Neutral.const name k univs) (arg :: args)

  partial def eval (term : Expr) (env : Env Value) : Value :=
    match term with
    | .app _ fnc arg =>
      let arg_thunk := Thunk.mk (fun _ => eval arg env)
      match eval fnc env with
      | Value.lam _ _ bod lam_env => eval bod (extEnv lam_env arg_thunk)
      | Value.app var@(Neutral.fvar ..) args => Value.app var (arg_thunk :: args)
      | Value.app (Neutral.const name k k_univs) args => applyConst name k k_univs arg_thunk args
      -- Since terms are well-typed we know that any other case is impossible
      | _ => panic! "Impossible eval case"
    | .lam _ name info _ bod => Value.lam name info bod env
    | .var _ _ idx =>
      let thunk := List.get! env.exprs idx
      thunk.get
    | .const _ name k const_univs => evalConst name k (List.map (instBulkReduce env.univs) const_univs)
    | .letE _ _ _ val bod =>
      let thunk := Thunk.mk (fun _ => eval val env)
      eval bod (extEnv env thunk)
    | .fix _ _ bod =>
      let thunk := Thunk.mk (fun _ => eval term env)
      eval bod (extEnv env thunk)
    | .pi _ name info dom img =>
      let dom := Thunk.mk (fun _ => eval dom env)
      Value.pi name info dom img env
    | .sort _ univ => Value.sort (instBulkReduce env.univs univ)
    | .lit _ lit => Value.lit lit
    | .lty _ lty => Value.lty lty
    | .proj _ idx expr =>
      let val := eval expr env
      match val with
      | .app (.const _ (.constructor _ ctor) _) args =>
        -- Since terms are well-typed, we can be sure that this constructor is of a structure-like inductive
        -- and, furthermore, that the index is in range of `args`
        let idx := ctor.params + idx
        (List.get! args idx).get
      | .app neu args => .proj idx neu args
      | _ => panic! "Impossible case on projections"
end

end Yatima.Typechecker
