import Yatima.Typechecker.TypecheckM
import Yatima.Typechecker.Printing

namespace Yatima.Typechecker

def derefConst (name : Name) (constIdx : ConstIdx) : TypecheckM Const := do
  let store := (← read).store
  match store.get? constIdx with
  | some const => pure const
  | none => throw $ .outOfConstsRange name constIdx store.size

mutual
  partial def evalConst (name : Name) (const : ConstIdx) (univs : List Univ) :
      TypecheckM Value := do
    match (← read).store.get! const with
    | .theorem x => withCtx ⟨[], univs⟩ $ eval x.value
    | .definition x =>
      match x.safety with
      | .safe => eval x.value
      | .partial => pure $ mkConst name const univs
      | .unsafe => throw .unsafeDefinition
    | _ => pure $ mkConst name const univs

  partial def applyConst (name : Name) (k : ConstIdx) (univs : List Univ)
      (arg : Thunk Value) (args : Args) : TypecheckM Value := do
    dbg_trace s!"Applying: {name}"
    -- Assumes a partial application of k to args, which means in particular,
    -- that it is in normal form
    match ← derefConst name k with
    | .intRecursor recur =>
      let major_idx := recur.params + recur.motives + recur.minors + recur.indices
      if args.length != major_idx then
        pure $ Value.app (Neutral.const name k univs) (arg :: args)
      else
        dbg_trace s!"Reached here: {arg.get} {args.map (·.get)}"
        match arg.get with
        | .app (Neutral.const k_name k _) args' => match ← derefConst k_name k with
          | .constructor ctor =>
            dbg_trace s!"ctor: {ctor.rhs}, {recur.indices}"
            let exprs := (args'.take ctor.fields) ++ (args.drop recur.indices)
            withCtx ⟨exprs, univs⟩ $ eval ctor.rhs
          | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
        | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | .extRecursor recur =>
      let major_idx := recur.params + recur.motives + recur.minors + recur.indices
      if args.length != major_idx then
        pure $ Value.app (Neutral.const name k univs) (arg :: args)
      else
        match arg.get with
        | .app (Neutral.const k_name k _) args' => match ← derefConst k_name k with
          | .constructor ctor =>
            -- TODO: if rules are in order of indices, then we can use an array instead of a list for O(1) referencing
            match recur.rules.find? (fun r => r.ctor.idx == ctor.idx) with
            | some rule =>
              let exprs := List.append (List.take rule.fields args') (List.drop recur.indices args)
              withCtx ⟨exprs, univs⟩ $ eval rule.rhs
            -- Since we assume expressions are previously type checked, we know that this constructor
            -- must have an associated recursion rule
            | none => throw .hasNoRecursionRule --panic! "Constructor has no associated recursion rule. Implementation is broken."
          | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
        | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | .quotient quotVal => match quotVal.kind with
      | .lift => reduceQuot arg args 6 1 $ Value.app (Neutral.const name k univs) (arg :: args)
      | .ind  => reduceQuot arg args 5 0 $ Value.app (Neutral.const name k univs) (arg :: args)
      | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)
    | _ => pure $ Value.app (Neutral.const name k univs) (arg :: args)

  partial def suspend (expr : Expr) (env : TypecheckEnv) : Thunk Value :=
    Thunk.mk fun _ => match TypecheckM.run env (eval expr) with
      | .ok a => a
      | .error e => .exception e

  partial def eval : Expr → TypecheckM Value
    | .app fnc arg => do
      let env ← read
      let arg_thunk := suspend arg env
      dbg_trace s!"Apply: {fnc} to {arg}"
      let fnc := (← eval fnc)
      dbg_trace s!"evaluated fnc: {fnc}"
      apply fnc arg_thunk
    | .lam name info _ bod => do
       let ctx := (← read).ctx
       pure $ Value.lam name info bod ctx
    | .var name idx => do
      let exprs := (← read).ctx.exprs
      let some thunk := exprs.get? idx | throw $ .outOfRangeError name idx exprs.length
      pure thunk.get
    | .const name k const_univs => do
      dbg_trace s!"Processing: {name}"
      let ctx := (← read).ctx
      evalConst name k (const_univs.map (instBulkReduce ctx.univs))
    | .letE _ _ val bod => do
      let thunk := suspend val (← read)
      withExtendedCtx thunk (eval bod)
    | .pi name info dom img => do
      let env ← read
      let dom' := suspend dom env
      pure $ Value.pi name info dom' img env.ctx
    | .sort univ => do
      let ctx := (← read).ctx
      pure $ Value.sort (instBulkReduce ctx.univs univ)
    | .lit lit => pure $ Value.lit lit
    | .lty lty => pure $ Value.lty lty
    | .proj idx expr => do
      match (← eval expr) with
      | .app neu@(.const name k _) args => 
        match ← derefConst name k with
        | .constructor ctor =>
          -- Since terms are well-typed, we can be sure that this constructor is of a structure-like inductive
          -- and, furthermore, that the index is in range of `args`
          let idx := ctor.params + idx
          let some arg := args.get? idx | throw $ .custom s!"Invalid projection of index {idx} but constructor has only {args.length} arguments"
          pure $ arg.get
        | _ => pure $ .proj idx neu args
      | .app neu args => pure $ .proj idx neu args
      | _ => throw .impossible

  partial def evalConst (name : Name) (const : ConstIdx) (univs : List Univ) :
      TypecheckM Value := do
    match ← derefConst name const with
    | .theorem x => withCtx ⟨[], univs⟩ $ eval x.value
    | .definition x =>
      match x.safety with
      | .safe => eval x.value
      | .partial => pure $ mkConst name const univs
      | .unsafe => throw .unsafeDefinition
    | _ => pure $ mkConst name const univs

  partial def apply (value : Value) (arg : Thunk Value) : TypecheckM Value :=
    match value with
    | .lam _ _ bod lamCtx => withNewExtendedCtx lamCtx arg (eval bod)
    | .app (.const name k k_univs) args' =>
      dbg_trace s!"HERE: {name}"
      applyConst name k k_univs arg args'
    | .app var@(.fvar ..) args' => pure $ Value.app var (arg :: args')
    -- Since terms are well-typed we know that any other case is impossible
    | _ => throw .impossible

  partial def reduceQuot (major? : Thunk Value) (args : Args) (reduceSize : Nat) (argPos : Nat) (default : Value) :
      TypecheckM Value :=
    let argsLength := args.length + 1
    if argsLength == reduceSize then
      match major?.get with
      | .app (.const name majorFn _) majorArgs => do
        match ← derefConst name majorFn with
        | Const.quotient {kind := QuotKind.ctor, ..} =>
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

end

end Yatima.Typechecker
