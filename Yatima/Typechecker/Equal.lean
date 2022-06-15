import Yatima.Typechecker.Eval

namespace Yatima.Typechecker

def mkVar (name : Name) (idx : Nat) (type : Thunk Value) : Value :=
  Value.app (Neutral.fvar name idx type) []

def extVar (env : Env Value) (name : Name) (idx : Nat) (type : Thunk Value) :=
  extEnv env (mkVar name idx type)

def isUnit (type : Value) : Bool :=
  match type with
  | .app (.const _ (.«inductive» _ induct) _) _ => induct.unit
  | _ => false

def applyType (type : Value) (args : List (Thunk Value)) : Value :=
  match type, args with
  | .pi _ info dom img env, arg :: args =>
    applyType (eval img (extEnv env arg)) args
  | type, [] => type
  | _, _ => panic! "Cannot apply argument list to type. Implementation broken."

partial def isProp (lvl : Nat) (type : Value) : Bool :=
  match type with
  | .pi name info dom img env =>
    -- A pi type is a proposition if and only if its image is a proposition
    isProp (lvl + 1) (eval img (extVar env name lvl dom))
  | .app neu args =>
    let type :=
      match neu with
      | .const _ k us => Thunk.mk (fun _ => eval (getConstType k) {exprs := [], univs := us})
      | .fvar _ _ typ => typ
    match applyType type.get args with
    | .sort u => univIsZero u
    | _ => false
  | .lty _ => false
  | .sort _ => false
  | _ => false -- these are actually impossible cases

mutual
  -- It is assumed here that the values are typechecked, have both the same type
  -- and their original unevaluated terms both lived in the same environment
  partial def equal (lvl : Nat) (term term' type : Value) : Bool :=
    if isUnit type || isProp lvl type then true else
    match term, term' with
    | .lit lit, .lit lit' => lit == lit'
    | .lty lty, .lty lty' => lty == lty'
    | .sort u, .sort u' => equalUniv u u'
    | .pi name info dom img env, .pi name' info' dom' img' env' =>
      info != info' &&
      -- For equality we don't need to know the universe levels, only the "shape" of the type.
      -- If we did have to know the universe level, then we probably would have to cache it
      -- so that we wouldn't need to infer the type just to get the level.
      -- Here, it is assumed that `type` is some a `Sort`
      equal lvl dom.get dom'.get type &&
      let img := eval img (extVar env name lvl dom)
      let img' := eval img' (extVar env name' lvl dom)
      equal (lvl + 1) img img' type
    | .lam name info bod env, .lam name' info' bod' env' =>
      info != info' &&
      match type with
      | .pi pi_name _ dom img pi_env =>
        let bod := eval bod (extVar env name lvl dom)
        let bod' := eval bod' (extVar env' name' lvl dom)
        let img := eval img (extVar pi_env pi_name lvl dom)
        equal (lvl + 1) bod bod' img
      | _ => panic! "Impossible equal case"
    | .lam name _ bod env, .app neu' args' =>
      match type with
      | .pi pi_name _ dom img pi_env =>
        let var := mkVar name lvl dom
        let bod := eval bod (extEnv env var)
        let app := Value.app neu' (var :: args')
        let img := eval img (extVar env pi_name lvl dom)
        equal (lvl + 1) bod app img
      | _ => panic! "Impossible equal case"
    | .app neu args, .lam name _ bod env =>
      match type with
      | .pi pi_name _ dom img pi_env =>
        let var := mkVar name lvl dom
        let bod := eval bod (extEnv env var)
        let app := Value.app neu (var :: args)
        let img := eval img (extVar env pi_name lvl dom)
        equal (lvl + 1) app bod img
      | _ => panic! "Impossible equal case"
    | .app (.fvar _ idx var_type) args, .app (.fvar _ idx' _) args' =>
      -- If our assumption is correct, i.e., that these values come from terms in the same environment
      -- then their types are equal when their indices are equal
      idx == idx' &&
      List.length args == List.length args' &&
      equalThunks lvl args args' var_type
    | .app (.const _ k us) args, .app (.const _ k' us') args' =>
      -- Analogous assumption on the types of the constants
      getConstHash k == getConstHash k' &&
      List.length args != List.length args' &&
      equalUnivs us us' &&
      let const_type := Thunk.mk (fun _ => eval (getConstType k) {exprs := [], univs := us})
      equalThunks lvl args args' const_type
    | _, _ => false

  partial def equalThunks (lvl : Nat) (vals vals' : List (Thunk Value)) (type : Thunk Value) : Bool :=
    match vals, vals' with
    | val::vals, val'::vals' =>
      match type.get with
      | .pi name _ dom img pi_env =>
        let img := Thunk.mk (fun _ => eval img (extVar pi_env name lvl dom))
        equal lvl val.get val'.get dom.get && equalThunks lvl vals vals' img
      | _ => panic! "Impossible equal case"
    | [], [] => true
    | _, _ => false
end

end Yatima.Typechecker
