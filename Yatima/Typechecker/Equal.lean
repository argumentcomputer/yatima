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
  partial def equal (info : TypeInfo) (lvl : Nat) (term term' : Value) : TypecheckM Bool := do
    if info.unit? || info.proof? then pure true else
    match term, term' with
    | .lit lit, .lit lit' => pure $ lit == lit'
    | .sort u, .sort u' => pure $ u.equalUniv u'
    | .pi name _ dom img env, .pi name' _ dom' img' env' => do
      let res  ← equal dom.info lvl dom.get dom'.get
      let imgInfo := img.info
      let img  ← withNewExtendedEnv env  (mkSusVar dom.info  name  lvl) $ eval img
      let img' ← withNewExtendedEnv env' (mkSusVar dom'.info name' lvl) $ eval img'
      let res' ← equal imgInfo (lvl + 1) img img'
      pure $ res && res'
    | .lam name _ dom bod env, .lam name' _ dom' bod' env' =>
      let res  ← equal dom.info lvl dom.get dom'.get
      let bodInfo := bod.info
      let bod  ← withNewExtendedEnv env  (mkSusVar dom.info  name  lvl) $ eval bod
      let bod' ← withNewExtendedEnv env' (mkSusVar dom'.info name' lvl) $ eval bod'
      let res' ← equal bodInfo (lvl + 1) bod bod'
      pure $ res && res'
    | .lam name _ dom bod env, .app neu' args' =>
      let var := mkSusVar dom.info name lvl
      let bodInfo := bod.info
      let bod ← withNewExtendedEnv env var (eval bod)
      let app := Value.app neu' (var :: args')
      equal bodInfo (lvl + 1) bod app
    | .app neu args, .lam name _ dom bod env =>
      let var := mkSusVar dom.info name lvl
      let bodInfo := bod.info
      let bod ← withNewExtendedEnv env var (eval bod)
      let app := Value.app neu (var :: args)
      equal bodInfo (lvl + 1) app bod
    | .app (.fvar _ idx) args, .app (.fvar _ idx') args' =>
      if idx == idx' then
        -- If our assumption is correct, i.e., that these values come from terms
        -- in the same environment then their types are equal when their indices
        -- are equal
        equalThunks lvl args args'
      else pure false
    | .app (.const _ k us) args, .app (.const _ k' us') args' =>
      if k == k' && Univ.equalUnivs us us' then
        equalThunks lvl args args'
      else pure false
    | .app (.proj idx val) args, .app (.proj idx' val') args' =>
      match val.info.struct?, val'.info.struct? with
      | .some const, .some const' =>
        if const == const' && idx == idx' then
          let eqVal ← equal val.info lvl val.get val'.get
          let eqThunks ← equalThunks lvl args args'
          pure (eqVal && eqThunks)
        else pure false
      | _, _ => throw $ .custom "Projection has been used on a non-structure value. Implementation broken"
    | _, _ => pure false

/--
Checks if two list of thunks `vals vals' : List SusValue` are equal by evaluating the thunks
and checking the evaluated images are equal.
-/
  partial def equalThunks (lvl : Nat) (vals vals' : List SusValue) : TypecheckM Bool :=
    match vals, vals' with
    | val::vals, val'::vals' => do
      let eq ← equal val.info lvl val.get val'.get
      let eq' ← equalThunks lvl vals vals'
      pure $ eq && eq'
    | [], [] => pure true
    | _, _ => pure false

end

end Yatima.Typechecker
