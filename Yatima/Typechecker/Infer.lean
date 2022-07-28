import Yatima.Typechecker.TypecheckM
import Yatima.Typechecker.Equal

namespace Yatima.Typechecker

def checkStructure (ind : Inductive) : TypecheckM Constructor :=
  match ind.struct with
  | some ctor => pure ctor
  | none => throw .typNotStructure

mutual

  partial def check (term : Expr) (type : Value) : TypecheckM Unit := do
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
      | _ => throw .notPi
    | .letE _ exp_typ exp bod =>
      match ← infer exp_typ with
      | Value.sort _ =>
        let exp_typ ← eval exp_typ
        check exp exp_typ
        let exp ← suspend exp (← read)
        extCtx exp exp_typ $ check bod type
      | _ => throw CheckError.notTyp
    | _ =>
      let infer_type ← infer term
      let sort := Value.sort Univ.zero
      if (← equal (← read).lvl type infer_type sort)
      then pure ()
      else throw .valueMismatch

  partial def infer (term : Expr) : TypecheckM Value := do
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
        let arg ← suspend arg (← read)
        let type ← withExtEnv env arg $ eval img
        pure type
      | _ => throw .notPi
    -- Should we add inference of lambda terms? Perhaps not on this checker,
    -- but on another that is capable of general unification, since this checker
    -- is supposed to be used on fully annotated terms.
    | .lam .. => throw .cannotInferLam
    | .pi name _ dom img  =>
      let dom_lvl ← match (← infer dom) with
        | .sort u => pure u
        | _ => throw .notTyp
      let ctx ← read
      let dom ← suspend dom ctx
      extCtx (mkVar name ctx.lvl dom) dom $ do
        let img_lvl ← match ← infer img with
          | .sort u => pure u
          | _ => throw CheckError.notTyp
        let lvl := reduceIMax dom_lvl img_lvl
        pure (Value.sort lvl)
    | .letE _ exp_typ exp bod =>
      match (← infer exp_typ) with
      | Value.sort _ =>
        let exp_typ ← eval exp_typ
        check exp exp_typ
        let exp ← suspend exp (← read)
        extCtx exp exp_typ $ infer bod
      | _ => throw CheckError.notTyp
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
            | none => throw .typNotStructure
          if ind.params != params.length then throw .valueMismatch else
          let mut ctorType ← applyType (← withEnv ⟨[], univs⟩ $ eval ctor.type) params
          for i in [:idx] do
            match ctorType with
            | .pi _ _ _ img pi_env =>
              let proj ← suspend (Expr.proj i expr) (← read)
              ctorType ← withExtEnv pi_env proj $ eval img
            | _ => pure ()
          match ctorType with
          | .pi _ _ dom _ _  =>
            let lvl := (← read).lvl
            let typ := dom.get
            if (← isProp lvl exprTyp) && !(← isProp lvl typ)
            then throw .projEscapesProp
            else pure typ
          | _ => throw .impossible
        | _ => throw .typNotStructure
      | _ => throw .typNotStructure

end

end Yatima.Typechecker
