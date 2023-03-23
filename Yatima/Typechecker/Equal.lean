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

/-- Reduces the application of a `pi` type to its arguments -/
def applyType : Value → List TypedValue → TypecheckM Value
  | .pi _ img imgCtx, arg :: args => do
    let res ← withEnv (imgCtx.extendWith arg) (eval img)
    applyType res args
  | type, [] => pure type
  | _, _ => throw "Invalid case for applyType"

mutual
  partial def tryEtaStruct (lvl : Nat) (term term' : TypedValue) : TypecheckM Bool := do
    match term'.body with
    | .app (.const k _) args _ =>
      match ← derefTypedConst k with
      | .constructor type .. =>
        match ← applyType (← eval type) args with
        | .app (.const tk _) args _ =>
          match ← derefTypedConst tk with
          | .inductive _ struct .. =>
            if struct then
              args.enum.foldlM (init := true) fun acc (i, arg) => do
                match arg.body with
                | .app (.proj _ idx val) _ _ =>
                  pure $ acc && i == idx && (← equal lvl term val)
                | _ => pure false
            else
              pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false

  /--
  Checks if two values `term term' : TypedValue` at level `lvl : Nat` are equal.

  It is assumed here that the values are typechecked, have both the same type and their
  original unevaluated terms both lived in the same context.
  -/
  partial def equal (lvl : Nat) (term term' : TypedValue) : TypecheckM Bool :=
    match term.info, term'.info with
    | .unit, .unit => pure true
    | .proof, .proof => pure true
    | _, _ => do
      match term.body, term'.body with
      | .lit lit, .lit lit' => pure $ lit == lit'
      | .sort u, .sort u' => pure $ u.equalUniv u'
      | .pi dom img env, .pi dom' img' env' => do
        let res  ← equal lvl dom dom'
        let img  ← withNewExtendedEnv env  (mkVar dom.info  lvl) $ evalTyped img
        let img' ← withNewExtendedEnv env' (mkVar dom'.info lvl) $ evalTyped img'
        let res' ← equal (lvl + 1) img img'
        pure $ res && res'
      | .lam dom bod env, .lam dom' bod' env' => do
        let res  ← equal lvl dom dom'
        let bod  ← withNewExtendedEnv env  (mkVar dom.info  lvl) $ evalTyped bod
        let bod' ← withNewExtendedEnv env' (mkVar dom'.info lvl) $ evalTyped bod'
        let res' ← equal (lvl + 1) bod bod'
        pure $ res && res'
      | .lam dom bod env, .app neu' args' infos' => do
        let var := mkVar dom.info lvl
        let bod  ← withNewExtendedEnv env var $ evalTyped bod
        let app := Value.app neu' (var :: args') (term'.info :: infos')
        equal (lvl + 1) bod (.mk bod.info app)
      | .app neu args infos, .lam dom bod env => do
        let var := mkVar dom.info lvl
        let bod  ← withNewExtendedEnv env var $ evalTyped bod
        let app := Value.app neu (var :: args) (term.info :: infos)
        equal (lvl + 1) (.mk bod.info app) bod
      | .app (.fvar idx) args _, .app (.fvar idx') args' _ =>
        if idx == idx' then
          -- If our assumption is correct, i.e., that these values come from terms
          -- in the same environment then their types are equal when their indices
          -- are equal
          equalValues lvl args args'
        else pure false
      | .app (.const k us) args _, .app (.const k' us') args' _ =>
        if k == k' && IR.Univ.equalUnivs us us' then
          equalValues lvl args args'
        else pure false
      | _, .app (.const _ _) _ _ =>
        tryEtaStruct lvl term term'
      | .app (.const _ _) _ _, _ =>
        tryEtaStruct lvl term' term
      | .app (.proj ind idx val) args _, .app (.proj ind' idx' val') args' _ =>
          if ind == ind' && idx == idx' then do
            let eqVal ← equal lvl val val'
            let eqVals ← equalValues lvl args args'
            pure (eqVal && eqVals)
          else pure false
      | _, _ =>
        pure false

/--
Checks if two list of values `vals vals' : List TypedValue` are equal
-/
  partial def equalValues (lvl : Nat) (vals vals' : List TypedValue) : TypecheckM Bool :=
    match vals, vals' with
    | val::vals, val'::vals' => do
      let eq ← equal lvl val val'
      let eq' ← equalValues lvl vals vals'
      pure $ eq && eq'
    | [], [] => pure true
    | _, _ => pure false

end

end Yatima.Typechecker
