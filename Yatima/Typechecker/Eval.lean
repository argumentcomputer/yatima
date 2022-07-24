import Yatima.Typechecker.CheckM

namespace Yatima.Typechecker

def mkConst (name : Name) (k : ConstIdx) (univs : List Univ) : Value :=
  Value.app (Neutral.const name k univs) []

def getValue : List (Thunk Value) → Nat → CheckM Value
  | a::_,  0   => pure a.get
  | _::as, n+1 => getValue as n
  | _,     _   => throw .outOfRangeError

def valueName (val : Value) : CheckM Name :=
  match val with
  | .lam name _ _ _ => pure name
  | .pi name _ _ _ _ => pure name
  | _ => throw .noName

-- The idea is taken from the Lean compiler,
-- see https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean#L705
private partial def mkAppRangeAux (n : Nat) (args : List (Thunk Value)) (i : Nat) (e : Neutral) : CheckM Value := do
  if i < n then do
    let ith_val ← getValue args i
    mkAppRangeAux n args (i + 1) (.fvar e.name i ith_val)
  else (pure $ Value.app e [])

def mkAppRange (f : Neutral) (i j : Nat) (args : List (Thunk Value)) : CheckM Value :=
  mkAppRangeAux j args i f

def getConst? (constName : Name) : CheckM (Option ConstantInfo) := sorry

mutual
  partial def evalConst (name : Name) (const : ConstIdx) (univs : List Univ) : CheckM Value := do
    match (← read).store.get! const with
    | .theorem x => withEnv ⟨[], univs⟩ $ eval x.value
    | .definition x =>
      match x.safety with
      | .safe => eval x.value
      | .partial => pure $ mkConst name const univs
      | .unsafe => throw .unsafeDefinition
    | _ => pure $ mkConst name const univs

  partial def applyConst (name : Name) (k : ConstIdx) (univs : List Univ) (arg : Thunk Value) (args : Args) : CheckM Value := do
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
            | none => throw .hasNoRecursionRule --panic! "Constructor has no associated recursion rule. Implementation is broken."
          | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
        | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | .quotient _ recVal =>
      -- This case is a version of the reduceQuotRec function from the Lean 4 source code
      -- https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/WHNF.lean#L203
      -- The case reduces ind and lift applications
      let process (majorPos argPos : Nat) : CheckM Value :=
        let arg_size := args.length + 1
        if h : majorPos < arg_size then do
          let major := (arg :: args).get ⟨ majorPos, h ⟩
          match major.get with
            | .app (.const majorFn _ _) [_, majorArg] => do
              --let .some (ConstantInfo.quotInfo { kind := QuotKind.ctor, .. }) ← getConst? majorFn
              -- TODO: figure out how to enable the line above
              let f := args[argPos]!
              let fName ← valueName f.get
              let r := (.fvar fName argPos f)
              let recArity := majorPos + 1
              mkAppRange r recArity args.length (majorArg :: args)
            -- TODO: more checking, this version is temporary, I got stuck here
            -- TODO: figure out do we need a version of getConstNoEx
            | _ => throw .cannotEvalQuotient
        else
          throw .cannotEvalQuotient
      match recVal.kind with
        | .lift => process 5 3
        | .ind  => process 4 3
        | _ => throw .cannotEvalQuotient
    | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)

  partial def suspend (expr : Expr) (ctx : Context) : Thunk Value :=
    Thunk.mk (fun _ => CheckM.run! (eval expr) ctx "Panic in eval. Implementation broken")

  partial def eval (term : Expr) : CheckM Value :=
    match term with
    | .app fnc arg => do
      let ctx ← read
      let arg_thunk := suspend arg ctx
      match (← eval fnc) with
      | Value.lam _ _ bod lam_env => withExtEnv lam_env arg_thunk (eval bod)
      | Value.app var@(Neutral.fvar ..) args => pure $ Value.app var (arg_thunk :: args)
      | Value.app (Neutral.const name k k_univs) args => applyConst name k k_univs arg_thunk args
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
      evalConst name k (List.map (instBulkReduce env.univs) const_univs)
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
      | _ => throw .impossibleProjectionCase --panic! "Impossible case on projections"

end

end Yatima.Typechecker
