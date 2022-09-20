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

def Yatima.TypeInfo.proofOrUnit? : TypeInfo → Bool
  | .UnitVal
  | .Proof => true
  | _ => false

namespace Yatima.Typechecker

mutual

  /--
  Checks if two values `term term' : Value` at level `lvl : Nat` are equal.

  It is assumed here that the values are typechecked, have both the same type `type`
  and their original unevaluated terms both lived in the same context.
  -/
  partial def equal (info : TypeInfo) (lvl : Nat) (term term' : Value) : TypecheckM Bool := do
    if info.proofOrUnit? then pure true else
    match term, term' with
    | .lit lit, .lit lit' => pure $ lit == lit'
    | .sort u, .sort u' => pure $ u.equalUniv u'
    | .pi name _ dom img env, .pi name' _ dom' img' env' => do
      let imgInfo := img.meta.info
      let img  ← withNewExtendedEnvByVar env  dom.info  name  lvl $ eval img
      let img' ← withNewExtendedEnvByVar env' dom'.info name' lvl $ eval img'
      let res  ← equal dom.info lvl dom.get dom'.get
      let res' ← equal imgInfo (lvl + 1) img img'
      pure $ res && res'
    | .lam name _ bod env, .lam name' _ bod' env' =>
      let bodInfo := bod.meta.info
      let bod  ← withNewExtendedEnvByVar env default name lvl $ eval bod
      let bod' ← withNewExtendedEnvByVar env' default name' lvl $ eval bod'
      equal bodInfo (lvl + 1) bod bod'
    | .lam name _ bod env, .app neu' args' =>
      -- sorry
      let var := (mkVar name lvl).toSusVal default s!"{name}"
      let bodInfo := bod.meta.info
      let bod ← withNewExtendedEnv env var (eval bod)
      let app := Value.app neu' (var :: args')
      equal bodInfo (lvl + 1) bod app
    | .app neu args, .lam name _ bod env =>
      -- sorry
      let var := (mkVar name lvl).toSusVal default s!"{name}"
      let bodInfo := bod.meta.info
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
    | .app (.proj idx val valInfo) args, .app (.proj idx' val' _) args' =>
      if idx == idx' then
        let eqVal ← equal valInfo lvl val val'
        let eqThunks ← equalThunks lvl args args'
        pure (eqVal && eqThunks)
      else pure false
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
