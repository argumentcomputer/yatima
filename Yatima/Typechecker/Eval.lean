import Yatima.Typechecker.Value

namespace Yatima.Typechecker

def mkConst (hash : Hash) (name : Name) (k : Const) (univs : List Univ) : Value :=
  Value.app (Neutral.const hash name k univs) []

mutual
partial def evalConst (hash : Hash) (name : Name) (const : Const) (univs : List Univ) : Value :=
  match const with
  | .«theorem» x =>
    eval x.value { exprs := [] , univs }
  | .definition x =>
    match x.safety with
    | .safe => eval x.value { exprs := [] , univs }
    | .«partial» => mkConst hash name const univs
    | .«unsafe» => panic! "Unsafe definition found"
  | _ => mkConst hash name const univs

  partial def applyConst (k_hash : Hash) (name : Name) (k : Const) (univs : List Univ) (arg : Thunk Value) (args : Args) : Value :=
  -- Assumes a partial application of k to args, which means in particular, that it is in normal form
    match k with
    | .recursor recur =>
      let major_idx := recur.params + recur.motives + recur.minors + recur.indices
      if args.length != major_idx then Value.app (Neutral.const k_hash name k univs) (arg :: args)
      else
        match arg.get with
        | Value.app (Neutral.const hash _ (.constructor ctor) _) args' =>
          match List.find? (fun r => r.fst == hash) recur.rules with
          | some (_, rule) =>
            let exprs := List.append (List.take rule.fields args') (List.drop recur.indices args)
            eval rule.rhs {exprs, univs}
          -- Since we assume expressions are previously type checked, we know that this constructor
          -- must have an associated recursion rule
          | none => panic! "Constructor has no associated recursion rule. Implementation is broken."
        | _ => Value.app (Neutral.const k_hash name k univs) (arg :: args)
    | _ => Value.app (Neutral.const k_hash name k univs) (arg :: args)

  partial def eval (term : Expr) (env : Env Value) : Value :=
    match term with
    | .app _ fnc arg =>
      let arg_thunk := Thunk.mk (fun _ => eval arg env)
      match eval fnc env with
      | Value.lam _ bod lam_env => eval bod {lam_env with exprs := arg_thunk :: lam_env.exprs}
      | Value.app var@(Neutral.fvar ..) args => Value.app var (arg_thunk :: args)
      | Value.app (Neutral.const hash name k k_univs) args => applyConst hash name k k_univs arg_thunk args
      -- Since terms are typed checked we know that any other case is impossible
      | _ => panic! "Impossible eval case"
    | .lam _ _ info _ bod => Value.lam info bod env
    | .var _ _ idx =>
      let thunk := List.get! env.exprs idx
      thunk.get
    | .const hash name k const_univs => evalConst hash name k (List.map (instBulkReduce env.univs) const_univs)
    | .letE _ _ _ val bod =>
      let thunk := Thunk.mk (fun _ => eval val env)
      eval bod {env with exprs := thunk :: env.exprs}
    | .fix _ _ bod =>
      let thunk := Thunk.mk (fun _ => eval term env)
      eval bod {env with exprs := thunk :: env.exprs}
    | .pi _ _ info dom img =>
      let dom := Thunk.mk (fun _ => eval dom env)
      Value.pi info dom img env
    | .sort _ univ => Value.sort (instBulkReduce env.univs univ)
    | .lit _ lit => Value.lit lit
    | .lty _ lty => Value.lty lty
    | .proj .. => panic! "TODO"
end

end Yatima.Typechecker
