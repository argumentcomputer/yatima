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

open TC

/-- Reduces the application of a `pi` type to its arguments -/
def applyType : Value → List SusValue → TypecheckM Value
  | .pi _ _ _ img imgCtx, arg :: args => do
    let res ← withEnv (imgCtx.extendWith arg) (eval img)
    applyType res args
  | type, [] => pure type
  | _, _ => throw .cannotApply

mutual
  partial def tryEtaStruct (lvl : Nat) (term term' : SusValue) : TypecheckM Bool := do
    match term'.get with
    | .app (.const name k _) args =>
      match ← derefTypedConst name k with
      | .constructor type .. =>
        match ← applyType (← eval type) args with
        | .app (.const tname tk _) args =>
          match ← derefTypedConst tname tk with
          | .inductive _ struct .. =>
            if struct then
              args.enum.foldlM (init := true) fun acc (i, arg) => do
                match arg.1.get with
                | .app (.proj _ idx val) _ =>
                pure $ acc && i == idx && (← equal lvl term val.sus)
                | _ => pure false
            else
              pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false

  /--
  Checks if two suspended values `term term' : SusValue` at level `lvl : Nat` are equal.

  It is assumed here that the values are typechecked, have both the same type and their
  original unevaluated terms both lived in the same context.
  -/
  partial def equal (lvl : Nat) (term term' : SusValue) : TypecheckM Bool := do
    match term.info, term'.info with
    | .unit, .unit => pure true
    | .proof, .proof => pure true
    | _, _ =>
      match term.get, term'.get with
      | .lit lit, .lit lit' => pure $ lit == lit'
      | .sort u, .sort u' => pure $ u.equalUniv u'
      | .pi name _ dom img env, .pi name' _ dom' img' env' => do
        let res  ← equal lvl dom dom'
        let img  := suspend img  { ← read with env := env.extendWith  (mkSusVar dom.info  name  lvl) } (← get)
        let img' := suspend img' { ← read with env := env'.extendWith (mkSusVar dom'.info name' lvl) } (← get)
        let res' ← equal (lvl + 1) img img'
        pure $ res && res'
      | .lam name _ dom bod env, .lam name' _ dom' bod' env' =>
        let res  ← equal lvl dom dom'
        let bod  := suspend bod  { ← read with env := env.extendWith  (mkSusVar dom.info  name  lvl) } (← get)
        let bod' := suspend bod' { ← read with env := env'.extendWith (mkSusVar dom'.info name' lvl) } (← get)
        let res' ← equal (lvl + 1) bod bod'
        pure $ res && res'
      | .lam name _ dom bod env, .app neu' args' =>
        let var := mkSusVar dom.info name lvl
        let bod  := suspend bod { ← read with env := env.extendWith var } (← get)
        let app := Value.app neu' ((var, bod.info) :: args')
        equal (lvl + 1) bod (.mk bod.info app)
      | .app neu args, .lam name _ dom bod env =>
        let var := mkSusVar dom.info name lvl
        let bod  := suspend bod { ← read with env := env.extendWith var } (← get)
        let app := Value.app neu ((var, bod.info) :: args)
        equal (lvl + 1) (.mk bod.info app) bod
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
      | _, .app (.const _ _ _) _ =>
        tryEtaStruct lvl term term'
      | .app (.const _ _ _) _, _ =>
        tryEtaStruct lvl term' term
      | .app (.proj ind idx val) args, .app (.proj ind' idx' val') args' =>
          if ind == ind' && idx == idx' then
            let eqVal ← equal lvl val.sus val'.sus
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
      let eq ← equal lvl val val'
      let eq' ← equalThunks lvl vals vals'
      pure $ eq && eq'
    | [], [] => pure true
    | _, _ => pure false

end

end Yatima.Typechecker
