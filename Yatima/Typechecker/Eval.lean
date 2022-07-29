import Yatima.Typechecker.TypecheckM

namespace Yatima.Typechecker

def mkConst (name : Name) (k : ConstIdx) (univs : List Univ) : Value :=
  Value.app (Neutral.const name k univs) []

def getValue : List (Thunk Value) → Nat → TypecheckM Value
  | a::_,  0   => pure a.get
  | _::as, n+1 => getValue as n
  | _,     _   => throw .outOfRangeError

def valueName : Value → TypecheckM Name
  | .lam name .. => pure name
  | .pi  name .. => pure name
  | _ => throw .noName

/--
The idea is taken from the Lean compiler,
see https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean#L705
-/
partial def mkAppRangeAux (n : Nat) (args : List (Thunk Value)) (i : Nat)
    (e : Neutral) : TypecheckM Value := do
  if i < n then do
    let ith_val ← getValue args i
    mkAppRangeAux n args (i + 1) (.fvar e.name i ith_val)
  else (pure $ Value.app e [])

def mkAppRange (f : Neutral) (i j : Nat) (args : List (Thunk Value)) :
    TypecheckM Value :=
  mkAppRangeAux j args i f

def getConst? (constName : Name) : TypecheckM (Option Const) := do
  let env ← read
  match env.find? constName with
    | x => pure x

/--
This case is a version of the reduceQuotRec function from the Lean 4 source code
https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/WHNF.lean#L203
The case reduces ind and lift applications
-/
def reduceQuot (arg : Thunk Value) (args : Args) (majorPos argPos : Nat) :
    TypecheckM Value :=
  let args' := arg :: args
  if h : majorPos < args'.length then
    let major := args'[majorPos]'h
    match major.get with
    | .app (.const majorFn _ _) [_, majorArg] => do
      let opConst ← getConst? majorFn
      match opConst with
      | .some (Const.quotient {kind := QuotKind.ctor, ..}) =>
        if h : argPos < args.length then
          let f := args[argPos]'h
          let fName ← valueName f.get
          let r := (Neutral.fvar fName argPos f)
          let recArity := majorPos + 1
          mkAppRange r recArity args.length (majorArg :: args)
        else throw .cannotEvalQuotient
      | _ => throw .noName
    | _ => throw .cannotEvalQuotient
  else
    throw .cannotEvalQuotient

mutual
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
      | .lift => reduceQuot arg args 5 3
      | .ind  => reduceQuot arg args 4 3
      | _ => throw .cannotEvalQuotient
    | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)

  partial def suspend (expr : Expr) (ctx : Context) : Thunk Value :=
    Thunk.mk (fun _ => 
      let value := match TypecheckM.run ctx (eval expr) with
      | .ok a => a
      | _ => .incorrectValue
      )

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
