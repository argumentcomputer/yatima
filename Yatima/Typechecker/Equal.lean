import Yatima.Typechecker.Eval

/-!
# Yatima typechecker: Equal

## Basic Structure

This is the second of the three main files that constitute the Yatima typechecker: `Eval`, `Equal`,
and `Infer`.

TODO: Add a high level overview of Equal in the contenxt of Eval-Equal-Infer.

## Equal

In this module the main function is `Yatima.Typechecker.equal` which checks whether two values are
equal. This is done case-by-case on the exact `val val' : Value` that are inputted:

* Literal equality can be handled
* Sorts are handled by `Yatima.Univ.equalUniv`
* `.lam` and `.pi`s are equal if their bodies are
* `.app` are handled by `Yatima.Typechecker.equalApp`

Note: Generally the values are assumed to already have the same type in the functions below.
-/

namespace Yatima.Typechecker

mutual

  /--
  Checks if two values `term term' : Value` at level `lvl : Nat` are equal.

  It is assumed here that the values are typechecked, have both the same type `type`
  and their original unevaluated terms both lived in the same context.
  -/
  partial def equal (lvl : Nat) (term term' : Value) : TypecheckM Bool := do
    if term.meta.proofOrUnit? then pure true else
    match term, term' with
    | .lit _ lit, .lit _ lit' => pure $ lit == lit'
    | .sort _ u, .sort _ u' => pure $ u.equalUniv u'
    | .pi _ name _ dom img env, .pi _ name' _ dom' img' env' => do
      -- The meta of these newly created variables does not matter, since the
      -- evaluation of the expressions variable will update the meta automatically
      let img  ← withNewExtendedEnvByVar env default name lvl $ eval img
      let img' ← withNewExtendedEnvByVar env' default name' lvl $ eval img'
      let res  ← equal lvl dom.get dom'.get
      let res' ← equal (lvl + 1) img img'
      pure $ res && res'
    | .lam _ name _ bod env, .lam _ name' _ bod' env' =>
      let bod  ← withNewExtendedEnvByVar env default name lvl $ eval bod
      let bod' ← withNewExtendedEnvByVar env' default name' lvl $ eval bod'
      equal (lvl + 1) bod bod'
    | .lam _ name _ bod env, .app _ neu' args' =>
      let var := mkVar default name lvl
      let bod ← withNewExtendedEnv env var (eval bod)
      let app := Value.app bod.meta neu' (var :: args')
      equal (lvl + 1) bod app
    | .app _ neu args, .lam _ name _ bod env =>
      let var := mkVar default name lvl
      let bod ← withNewExtendedEnv env var (eval bod)
      let app := Value.app bod.meta neu (var :: args)
      equal (lvl + 1) app bod
    | .app _ (.fvar _ idx) args, .app _ (.fvar _ idx') args' =>
      if idx == idx' then
        -- If our assumption is correct, i.e., that these values come from terms
        -- in the same environment then their types are equal when their indices
        -- are equal
        equalThunks lvl args args'
      else pure false
    | .app _ (.const _ k us) args, .app _ (.const _ k' us') args' =>
      if k == k' && Univ.equalUnivs us us' then
        equalThunks lvl args args'
      else pure false
    | .app _ (.proj idx val) args, .app _ (.proj idx' val') args' =>
      if idx == idx' then
        let eqVal ← equal lvl val val'
        let eqThunks ← equalThunks lvl args args'
        pure (eqVal && eqThunks)
      else pure false
    | _, _ => pure false

/--
Checks if two list of thunks `vals vals' : List (Thunk Value)` are equal by evaluating the thunks
and checking the evaluated images are equal.
-/
  partial def equalThunks (lvl : Nat) (vals vals' : List (Thunk Value)) : TypecheckM Bool :=
    match vals, vals' with
    | val::vals, val'::vals' => do
      let eq ← equal lvl val.get val'.get
      let eq' ← equalThunks lvl vals vals'
      pure $ eq && eq'
    | [], [] => pure true
    | _, _ => pure false

end

end Yatima.Typechecker
