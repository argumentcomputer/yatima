import Yatima.Typechecker.Eval

namespace Yatima.Typechecker

/-- Checks if a type is an unit inductive -/
def isUnit : Value → TypecheckM Bool
  | .app (.const name i _) _ => do
    match ← derefConst name i with
    | .inductive induct => pure induct.unit
    | _ => pure false
  | _ => pure false

def applyType : Value → List (Thunk Value) → TypecheckM Value
  | .pi _ _ _ img imgEnv, arg :: args => do
    let res ← withCtx (imgEnv.extendWith arg) (eval img)
    applyType res args
  | type, [] => pure type
  | _, _ => throw .cannotApply

partial def isProp (lvl : Nat) : Value → TypecheckM Bool
  | .pi name _ dom img env => do
    let res ← withNewExtendedCtxByVar env name lvl dom $ eval img
    -- A pi type is a proposition if and only if its image is a proposition
    isProp (lvl + 1) res
  | .app neu args => do
    let type ← match neu with
      | .const k_name k us => do
        let const := ← derefConst k_name k
        let env := { (← read) with ctx := ⟨ [], us ⟩ }
        pure $ suspend const.type env
      | .fvar _ _ typ => pure typ
    match ← applyType type.get args with
    | .sort u => pure $ univIsZero u
    | _ => pure false
  | .lty _ => pure false
  | .sort _ => pure false
  | _ => pure false -- these are actually impossible cases

mutual

  -- It is assumed here that the values are typechecked, have both the same type
  -- and their original unevaluated terms both lived in the same environment
  partial def equal (lvl : Nat) (term term' type : Value) : TypecheckM Bool := do
    let isU ← isUnit type
    let isP ← isProp lvl type
    if isU || isP then pure true else
    match term, term' with
    | .lit lit, .lit lit' => pure $ lit == lit'
    | .lty lty, .lty lty' => pure $ lty == lty'
    | .sort u, .sort u' => pure $ equalUniv u u'
    | .pi name _ dom img ctx, .pi name' _ dom' img' ctx' => do
      -- For equality we don't need to know the universe levels, only the "shape" of the type.
      -- If we did have to know the universe level, then we probably would have to cache it
      -- so that we wouldn't need to infer the type just to get the level.
      -- Here, it is assumed that `type` is some a `Sort`
      let img  ← withNewExtendedCtxByVar ctx name lvl dom $ eval img
      let img' ← withNewExtendedCtxByVar ctx' name' lvl dom $ eval img'
      let res  ← equal lvl dom.get dom'.get type
      let res' ← equal (lvl + 1) img img' type
      pure $ res && res'
    | .lam name _ bod ctx, .lam name' _ bod' ctx' =>
      match type with
      | .pi pi_name _ dom img piCtx => do
        let bod  ← withNewExtendedCtxByVar ctx name lvl dom $ eval bod
        let bod' ← withNewExtendedCtxByVar ctx' name' lvl dom $ eval bod'
        let img  ← withNewExtendedCtxByVar piCtx pi_name lvl dom $ eval img
        equal (lvl + 1) bod bod' img
      | _ => throw .impossible
    | .lam name _ bod env, .app neu' args' =>
      match type with
      | .pi pi_name _ dom img piCtx =>
        let var := mkVar name lvl dom
        let bod ← withNewExtendedCtx env var (eval bod)
        let app := Value.app neu' (var :: args')
        let img ← withNewExtendedCtxByVar piCtx pi_name lvl dom $ eval img
        equal (lvl + 1) bod app img
      | _ => throw .impossible
    | .app neu args, .lam name _ bod ctx =>
      match type with
      | .pi pi_name _ dom img pi_env =>
        let var := mkVar name lvl dom
        let bod ← withNewExtendedCtx ctx var (eval bod)
        let app := Value.app neu (var :: args)
        let img ← withNewExtendedCtxByVar pi_env pi_name lvl dom $ eval img
        equal (lvl + 1) app bod img
      | _ => throw .impossible
    | .app (.fvar _ idx var_type) args, .app (.fvar _ idx' _) args' =>
      -- If our assumption is correct, i.e., that these values come from terms
      -- in the same environment then their types are equal when their indices
      -- are equal
      let eq ← equalThunks lvl args args' var_type
      pure $ idx == idx' &&
      List.length args == List.length args' && eq
    | .app (.const _ k us) args, .app (.const _ k' us') args' =>
      equalApp lvl k k' us us' args args'
    | .proj idx (.const _ k us) args, .proj idx' (.const _ k' us') args' =>
      let eq ← equalApp lvl k k' us us' args args'
      pure $ idx == idx' && eq
    | _, _ => pure false

  partial def equalApp (lvl : Nat) (k k' : ConstIdx)
      (us us' : List Univ) (args args' : Args) : TypecheckM Bool := do
    -- Analogous assumption on the types of the constants
    let const := (← read).store.get! k
    let env := { (← read) with ctx := ⟨ [], us ⟩ }
    pure $
      k == k' &&
      List.length args == List.length args' &&
      equalUnivs us us' &&
      (← equalThunks lvl args args' (suspend const.type env))

  partial def equalThunks (lvl : Nat) (vals vals' : List (Thunk Value))
      (type : Thunk Value) : TypecheckM Bool :=
    match vals, vals' with
    | val::vals, val'::vals' =>
      match type.get with
      | .pi name _ dom img piCtx => do
        let img ← withNewExtendedCtxByVar piCtx name lvl dom $ eval img
        let eq ← equal lvl val.get val'.get dom.get
        let eq' ← equalThunks lvl vals vals' img
        pure $ eq && eq'
      | _ => throw .impossible
    | [], [] => pure true
    | _, _ => pure false

end

end Yatima.Typechecker
