import Yatima.Typechecker.CheckM
import Yatima.Typechecker.Equal

namespace Yatima.Typechecker

mutual

  partial def check (term : Expr) (type : Value) : CheckM Unit := do
    match term with
    | .lam _ lam_name _ _lam_dom bod => do
      match type with
      | .pi _ _ dom img env =>
        -- TODO check that `lam_dom` == `dom`
        -- though this is wasteful, since this would force
        -- `dom`, which might not need to be evaluated.
        let var := mkVar lam_name (← read).lvl dom
        let eval' ← extEnvHelper var $ eval img
        extCtx var dom $ check bod eval'
      | _ => throw .notPi
    | .letE _ _ exp_typ exp bod =>
      match (← infer exp_typ) with
      | Value.sort _ =>
        let exp_typ ← eval exp_typ
        check exp exp_typ
        let exp' ← eval exp
        let exp := Thunk.mk (fun _ => exp')
        let exp_typ := Thunk.mk (fun _ => exp_typ)
        extCtx exp exp_typ $ check bod type
      | _ => throw CheckError.notTyp
    | .fix _ _ bod => do
      -- IMPORTANT: We assume that we only reduce terms after they are type checked, though here
      -- we create a thunk for an evaluation of a term before finishing its checking. How can we
      -- make sure that we only evaluate this thunk when the term is checked?
      let eval' ← eval term
      let itself := Thunk.mk (fun _ => eval')
      extCtx itself type $ check bod type
    | _ =>
      let infer_type ← infer term
      if (← equal (← read).lvl type infer_type (Value.sort Univ.zero))
      then pure ()
      else throw .valueMismatch

  partial def infer (term : Expr) : CheckM Value := do
    match term with
    | .var _ _ idx =>
      let type := List.get! (← read).types idx
      pure type.get
    | .sort _ lvl =>
      let type := Value.sort (Univ.succ lvl)
      pure type
    | .app _ fnc arg =>
      let fnc_typ ← infer fnc
      match fnc_typ with
      | .pi _ _ dom img env =>
        check arg dom.get
        let eval' ← eval arg
        let arg := Thunk.mk (fun _ => eval')
        let type ← extEnvHelper arg $ eval img
        pure type
      | _ => throw .notPi
    -- Should we add inference of lambda terms? Perhaps not on this checker,
    -- but on another that is capable of general unification, since this checker
    -- is supposed to be used on fully annotated terms.
    | .lam .. => throw .cannotInferLam
    | .pi _ name _ dom img  =>
      let dom_lvl ← match (← infer dom) with
        | .sort u => pure u
        | _ => throw .notTyp
      let ctx ← read
      let eval' ← eval dom
      let dom := Thunk.mk (fun _ => eval')
      extCtx (mkVar name ctx.lvl dom) dom $ do
      let img_lvl ← match (← infer img) with
        | .sort u => pure u
        | _ => throw CheckError.notTyp
      pure (Value.sort (Univ.imax dom_lvl img_lvl))
    | .letE _ _ exp_typ exp bod =>
      match (← infer exp_typ) with
      | Value.sort _ =>
        let exp_typ ← eval exp_typ
        check exp exp_typ
        let eval' ← eval exp
        let exp := Thunk.mk (fun _ => eval')
        let exp_typ := Thunk.mk (fun _ => exp_typ)
        extCtx exp exp_typ $ infer bod
      | _ => throw CheckError.notTyp
    | .fix .. => throw CheckError.cannotInferFix
    | .lit _ (Literal.nat _) => pure $ Value.lty LitType.nat
    | .lit _ (Literal.str _) => pure $ Value.lty LitType.str
    | .lty .. => pure $ Value.sort (Univ.succ Univ.zero)
    | .const _ _ k const_univs =>
      let univs := (← read).env.univs
      let env := { exprs := [], univs := List.map (instBulkReduce univs) const_univs }
      eval (getConstType k) env
    | .proj nam idx expr =>
      let exprTyp ← infer expr
      match exprTyp with
      | .app (.const _ (.inductive _ ind) univs) params =>
        let ctor ← checkStructure ind
        if ind.params != params.length then throw .valueMismatch else
        let mut ctorType := applyType (← eval ctor.type { exprs := [], univs }) params
        for i in [:idx] do
          match (← ctorType) with
          | .pi _ _ _ img pi_env =>
            let env := (← read).env
            let eval' ← eval (Expr.proj nam i expr) env
            let proj := Thunk.mk (fun _ => eval')
            ctorType := eval img { pi_env with exprs := proj :: pi_env.exprs }
          | _ => pure ()
        match (← ctorType) with
        | .pi _ _ dom _ _  =>
          let lvl := (← read).lvl
          let typ := dom.get
          if (← isProp lvl exprTyp) && !(← isProp lvl typ)
          then throw .projEscapesProp
          else pure typ
        | _ => throw .impossible
      | _ => throw .typNotStructure

end

end Yatima.Typechecker
