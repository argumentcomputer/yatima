import Yatima.Typechecker.Equal

namespace Yatima.Typechecker

mutual

  partial def check (term : Expr) (type : Value) : TypecheckM Unit := do
    match term with
    | .lam lam_name _ _lam_dom bod => do
      match type with
      | .pi _ _ dom img ctx =>
        -- TODO check that `lam_dom` == `dom`
        -- though this is wasteful, since this would force
        -- `dom`, which might not need to be evaluated.
        let var := mkVar lam_name (← read).lvl dom
        let img ← withNewExtendedCtx ctx var $ eval img
        withExtendedEnv var dom $ check bod img
      | val => throw $ .notPi (printVal val)
    | .letE _ exp_typ exp bod =>
      discard $ isSort exp_typ
      let exp_typ ← eval exp_typ
      check exp exp_typ
      let exp := suspend exp (← read)
      withExtendedEnv exp exp_typ $ check bod type
    | _ =>
      let inferType ← infer term
      let sort := Value.sort Univ.zero
      if (← equal (← read).lvl type inferType sort)
      then pure ()
      else throw $ .valueMismatch (printVal inferType) (printVal type)

  partial def infer (term : Expr) : TypecheckM Value := do
    match term with
    | .var name idx =>
      let types := (← read).types
      let some type := types.get? idx | throw $ .outOfContextRange name idx types.length
      pure type.get
    | .sort lvl =>
      let lvl := Univ.instBulkReduce (← read).ctx.univs lvl.succ
      pure $ Value.sort lvl
    | .app fnc arg =>
      let fnc_typ ← infer fnc
      match fnc_typ with
      | .pi _ _ dom img ctx =>
        check arg dom.get
        let arg := suspend arg (← read)
        let type ← withNewExtendedCtx ctx arg $ eval img
        pure type
      | val => throw $ .notPi (printVal val)
    -- Should we add inference of lambda terms? Perhaps not on this checker,
    -- but on another that is capable of general unification, since this checker
    -- is supposed to be used on fully annotated terms.
    | .lam .. => throw .cannotInferLam
    | .pi name _ dom img  =>
      let dom_lvl ← isSort dom
      let ctx ← read
      let dom := suspend dom ctx
      withExtendedEnv (mkVar name ctx.lvl dom) dom $ do
        let img_lvl ← isSort img
        let lvl := Univ.reduceIMax dom_lvl img_lvl
        pure (Value.sort lvl)
    | .letE _ exp_typ exp bod =>
      discard $ isSort exp_typ
      let exp_typ ← eval exp_typ
      check exp exp_typ
      let exp := suspend exp (← read)
      withExtendedEnv exp exp_typ $ infer bod
    | .lit (.num _) => pure $ Value.lty .num
    | .lit (.word _) => pure $ Value.lty .word
    | .lty .. => pure $ Value.sort (Univ.succ Univ.zero)
    | .const name k constUnivs =>
      let univs := (← read).ctx.univs
      let const ← derefConst name k
      withCtx ⟨[], constUnivs.map (Univ.instBulkReduce univs)⟩ $ eval const.type
    | .proj idx expr =>
      let exprTyp ← infer expr
      match exprTyp with
      | .app (.const name k univs) params =>
        match ← derefConst name k with
        | .inductive ind => do
          let ctor ← match ind.struct with
            | some ctor => pure ctor
            | none => throw $ .typNotStructure (printVal exprTyp)
          if ind.params != params.length then throw .impossible else
          let mut ctorType ← applyType (← withCtx ⟨[], univs⟩ $ eval ctor.type) params
          for i in [:idx] do
            match ctorType with
            | .pi _ _ _ img piCtx =>
              let proj := suspend (Expr.proj i expr) (← read)
              ctorType ← withNewExtendedCtx piCtx proj $ eval img
            | _ => pure ()
          match ctorType with
          | .pi _ _ dom _ _  =>
            let lvl := (← read).lvl
            let typ := dom.get
            if (← isProp lvl exprTyp) && !(← isProp lvl typ)
            then throw $ .projEscapesProp (printExpr term)
            else pure typ
          | _ => throw .impossible
        | _ => throw $ .typNotStructure (printVal exprTyp)
      | _ => throw $ .typNotStructure (printVal exprTyp)

  partial def isSort (expr : Expr) : TypecheckM Univ := do
    match ← infer expr with
      | .sort u => pure u
      | val => throw $ .notTyp (printVal val)

end

def checkValueType (name : Name) (value type : Expr) : TypecheckM Unit := do
  discard $ isSort type
  let trace := fun e => dbg_trace s!"✗ {name} : {type}"; throw e
  tryCatch (check value (← eval type)) trace
  dbg_trace s!"✓ {name} : {type}"

def checkConst : Const → TypecheckM Unit
  | .axiom       struct => do
    let trace := fun e => dbg_trace s!"✗ {struct.name} : {struct.type}"; throw e
    tryCatch (discard $ isSort struct.type) trace
    dbg_trace s!"✓ {struct.name} : {struct.type}"
  | .theorem     struct => checkValueType struct.name struct.value struct.type
  | .opaque      struct => checkValueType struct.name struct.value struct.type
  | .definition  struct => checkValueType struct.name struct.value struct.type
  -- TODO: check that inductives, constructors and recursors are well-formed
  | .inductive   struct => dbg_trace s!"✓ {struct.name} : {struct.type}"; pure ()
  | .constructor struct => dbg_trace s!"✓ {struct.name} : {struct.type}"; pure ()
  | .extRecursor struct => dbg_trace s!"✓ {struct.name} : {struct.type}"; pure ()
  | .intRecursor struct => dbg_trace s!"✓ {struct.name} : {struct.type}"; pure ()
  -- TODO: check that quotient is well-formed. I guess it is possible to do this while converting from Ipld
  -- by checking the cids of the quotient constants with precomputed ones
  | .quotient    struct => dbg_trace s!"✓ {struct.name} : {struct.type}"; pure ()

end Yatima.Typechecker
