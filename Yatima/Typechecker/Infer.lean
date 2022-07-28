import Yatima.Typechecker.TypecheckM
import Yatima.Typechecker.Equal
import Yatima.Typechecker.Printing

namespace Yatima.Typechecker

mutual

  partial def check (term : Expr) (type : Value) : TypecheckM Unit := do
    dbg_trace "checking {term} against {type}"
    match term with
    | .lam lam_name _ _lam_dom bod => do
      match type with
      | .pi _ _ dom img env =>
        -- TODO check that `lam_dom` == `dom`
        -- though this is wasteful, since this would force
        -- `dom`, which might not need to be evaluated.
        let var := mkVar lam_name (← read).lvl dom
        let img ← withExtEnv env var $ eval img
        extCtx var dom $ check bod img
      | val => throw $ .notPi val
    | .letE _ exp_typ exp bod =>
      let _ := isSort exp_typ
      let exp_typ ← eval exp_typ
      check exp exp_typ
      let exp := suspend exp (← read)
      extCtx exp exp_typ $ check bod type
    | _ =>
      let infer_type ← infer term
      let sort := Value.sort Univ.zero
      if (← equal (← read).lvl type infer_type sort)
      then pure ()
      else throw $ .valueMismatch infer_type type

  partial def infer (term : Expr) : TypecheckM Value := do
    dbg_trace "infering {term}"
    match term with
    | .var _ idx =>
      let type := List.get! (← read).types idx
      pure type.get
    | .sort lvl =>
      let lvl := instBulkReduce (← read).env.univs (Univ.succ lvl)
      pure $ Value.sort lvl
    | .app fnc arg =>
      let fnc_typ ← infer fnc
      match fnc_typ with
      | .pi _ _ dom img env =>
        check arg dom.get
        let arg := suspend arg (← read)
        let type ← withExtEnv env arg $ eval img
        pure type
      | val => throw $ .notPi val
    -- Should we add inference of lambda terms? Perhaps not on this checker,
    -- but on another that is capable of general unification, since this checker
    -- is supposed to be used on fully annotated terms.
    | .lam .. => throw .cannotInferLam
    | .pi name _ dom img  =>
      let dom_lvl ← isSort dom
      let ctx ← read
      let dom := suspend dom ctx
      extCtx (mkVar name ctx.lvl dom) dom $ do
        let img_lvl ← isSort img
        let lvl := reduceIMax dom_lvl img_lvl
        pure (Value.sort lvl)
    | .letE _ exp_typ exp bod =>
      let _ := isSort exp_typ
      let exp_typ ← eval exp_typ
      check exp exp_typ
      let exp := suspend exp (← read)
      extCtx exp exp_typ $ infer bod
    | .lit (Literal.nat _) => pure $ Value.lty LitType.nat
    | .lit (Literal.str _) => pure $ Value.lty LitType.str
    | .lty .. => pure $ Value.sort (Univ.succ Univ.zero)
    | .const _ k const_univs =>
      let univs := (← read).env.univs
      let const := (← read).store.get! k
      withEnv ⟨[], (List.map (instBulkReduce univs) const_univs)⟩ $ eval const.type
    | .proj idx expr =>
      let exprTyp ← infer expr
      match exprTyp with
      | .app (.const _ const univs) params => match (← read).store.get! const with
        | .inductive ind => do
          let ctor ← match ind.struct with
            | some ctor => pure ctor
            | none => throw $ .typNotStructure exprTyp
          if ind.params != params.length then throw .impossible else
          let mut ctorType ← applyType (← withEnv ⟨[], univs⟩ $ eval ctor.type) params
          for i in [:idx] do
            match ctorType with
            | .pi _ _ _ img pi_env =>
              let proj := suspend (Expr.proj i expr) (← read)
              ctorType ← withExtEnv pi_env proj $ eval img
            | _ => pure ()
          match ctorType with
          | .pi _ _ dom _ _  =>
            let lvl := (← read).lvl
            let typ := dom.get
            if (← isProp lvl exprTyp) && !(← isProp lvl typ)
            then throw $ .projEscapesProp term
            else pure typ
          | _ => throw .impossible
        | _ => throw $ .typNotStructure exprTyp
      | _ => throw $ .typNotStructure exprTyp

  partial def isSort (expr : Expr) : TypecheckM Univ := do
    match ← infer expr with
      | .sort u => pure u
      | val => throw $ .notTyp val

end

def checkValueType (value type : Expr) : TypecheckM Unit := do
  let univ ← isSort type
  tryCatch (check value (.sort univ)) (fun e => dbg_trace s!"✗ {value} : {type}"; throw e)
  dbg_trace s!"✓ {value} : {type}"

def checkConst : Const → TypecheckM Unit
  | .axiom      struct => discard $ isSort struct.type
  | .theorem    struct => checkValueType struct.value struct.type
  | .opaque     struct => checkValueType struct.value struct.type
  | .definition struct => checkValueType struct.value struct.type
  -- TODO: check that inductives, constructors and recursors are well-formed
  | .inductive       _ => pure ()
  | .constructor     _ => pure ()
  | .extRecursor     _ => pure ()
  | .intRecursor     _ => pure ()
  -- TODO: check that quotient is well-formed. I guess it is possible to do this while converting from Ipld
  -- by checking the cids of the quotient constants with precomputed ones
  | .quotient        _ => pure ()

end Yatima.Typechecker
