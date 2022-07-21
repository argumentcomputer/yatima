import Yatima.Typechecker.CheckM
import Yatima.Typechecker.Eval

namespace Yatima.Typechecker

def mkVar (name : Name) (idx : Nat) (type : Thunk Value) : Value :=
  Value.app (Neutral.fvar name idx type) []

def extVar  (name : Name) (idx : Nat) (type : Thunk Value) : CheckM Value → CheckM Value :=
  withReader (fun ctx => { ctx with env := extEnv ctx.env (mkVar name idx type) })

def isUnit (type : Value) : Bool :=
  match type with
  | .app (.const _ (.inductive _ induct) _) _ => induct.unit
  | _ => false

def applyType (type : Value) (args : List (Thunk Value)) : CheckM Value :=
  match type, args with
  | .pi _ _ _ img _, arg :: args => do
    let res ← extEnvHelper arg (eval img)
    applyType res args
  | type, [] => pure type
  | _, _ => throw .cannotApply

partial def isProp (lvl : Nat) (type : Value) : CheckM Bool :=
  match type with
  | .pi name _ dom img _ => do
    let res ← extVar name lvl dom $ eval img
    -- A pi type is a proposition if and only if its image is a proposition
    isProp (lvl + 1) res
  | .app neu args => do
    let type :=
      match neu with
      | .const _ k us => do
           let res ← eval (getConstType k) --{exprs := [], univs := us}
           pure $ Thunk.mk (fun _ => res)
      | .fvar _ _ typ => pure typ
    let t ← type
    match (← applyType t.get args) with
    | .sort u => pure $ univIsZero u
    | _ => pure false
  | .lty _ => pure false
  | .sort _ => pure false
  | _ => pure false -- these are actually impossible cases

mutual

  -- It is assumed here that the values are typechecked, have both the same type
  -- and their original unevaluated terms both lived in the same environment
  partial def equal (lvl : Nat) (term term' type : Value) : CheckM Bool := do
    let isP ← isProp lvl type
    if isUnit type || isP then pure true else
    match term, term' with
    | .lit lit, .lit lit' => pure $ lit == lit'
    | .lty lty, .lty lty' => pure $ lty == lty'
    | .sort u, .sort u' => pure $ equalUniv u u'
    | .pi name _ dom img _, .pi name' _ dom' img' _ => do
      -- For equality we don't need to know the universe levels, only the "shape" of the type.
      -- If we did have to know the universe level, then we probably would have to cache it
      -- so that we wouldn't need to infer the type just to get the level.
      -- Here, it is assumed that `type` is some a `Sort`
      let img ← extVar name lvl dom $ eval img
      let img' ← extVar name' lvl dom $ eval img'
      let res ← equal lvl dom.get dom'.get type
      let res' ← equal (lvl + 1) img img' type
      pure $ res && res'
    | .lam name _ bod _, .lam name' _ bod' _ =>
      match type with
      | .pi pi_name _ dom img _ => do
        let bod ←  extVar name lvl dom $ eval bod
        let bod' ← extVar name' lvl dom $ eval bod'
        let img ← extVar pi_name lvl dom $ eval img
        equal (lvl + 1) bod bod' img
      | _ => throw .impossibleEqualCase
    | .lam name _ bod _, .app neu' args' =>
      match type with
      | .pi pi_name _ dom img _ =>
        let var := mkVar name lvl dom
        let bod ← extEnvHelper var (eval bod)
        let app := Value.app neu' (var :: args')
        let img ← extVar pi_name lvl dom $ eval img
        equal (lvl + 1) bod app img
      | _ => throw .impossibleEqualCase
    | .app neu args, .lam name _ bod _ =>
      match type with
      | .pi pi_name _ dom img _ =>
        let var := mkVar name lvl dom
        let bod ← extEnvHelper var (eval bod)
        let app := Value.app neu (var :: args)
        let img ← extVar pi_name lvl dom $ eval img
        equal (lvl + 1) app bod img
      | _ => throw .impossibleEqualCase
    | .app (.fvar _ idx var_type) args, .app (.fvar _ idx' _) args' =>
      -- If our assumption is correct, i.e., that these values come from terms in the same environment
      -- then their types are equal when their indices are equal
      let eq ← equalThunks lvl args args' var_type
      pure $ idx == idx' &&
      List.length args == List.length args' && eq
    | .app (.const _ k us) args, .app (.const _ k' us') args' =>
      equalApp lvl k k' us us' args args'
    | .proj idx (.const _ k us) args, .proj idx' (.const _ k' us') args' =>
      let eq ← equalApp lvl k k' us us' args args'
      pure $ idx == idx' && eq
    | _, _ => pure false

  partial def equalApp (lvl : Nat) (k k' : Const)
      (us us' : List Univ) (args args' : Args) : CheckM Bool := do
    -- Analogous assumption on the types of the constants
    let res ← eval (getConstType k) --{exprs := [], univs := us}
    let const_type := Thunk.mk (fun _ => res)
    let eq ← equalThunks lvl args args' const_type
    pure $
    getConstHash k == getConstHash k' &&
    List.length args != List.length args' &&
    equalUnivs us us' &&
    eq

  partial def equalThunks (lvl : Nat) (vals vals' : List (Thunk Value))
      (type : Thunk Value) : CheckM Bool :=
    match vals, vals' with
    | val::vals, val'::vals' =>
      match type.get with
      | .pi name _ dom img _ => do
        let res ← extVar name lvl dom $ eval img
        let img := Thunk.mk (fun _ => res)
        let eq ← equal lvl val.get val'.get dom.get
        let eq' ← equalThunks lvl vals vals' img
        pure $ eq && eq'
      | _ => throw .impossibleEqualCase
    | [], [] => pure true
    | _, _ => pure false

end

end Yatima.Typechecker
