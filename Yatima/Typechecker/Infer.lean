import Yatima.Typechecker.Equal

namespace Yatima.Typechecker

mutual

  partial def check (term : Expr) (type : Value) : TypecheckM Unit := do
    match term with
    | .lam lamName _ _lamDom bod =>
      match type with
      | .pi _ _ dom img ctx =>
        -- TODO check that `lamDom` == `dom`
        -- though this is wasteful, since this would force
        -- `dom`, which might not need to be evaluated.
        let var := mkVar lamName (← read).lvl dom
        let img ← withNewExtendedCtx ctx var $ eval img
        withExtendedEnv var dom $ check bod img
      | val => throw $ .notPi (printVal val)
    | .letE _ expType exp bod =>
      discard $ isSort expType
      let expType ← eval expType
      check exp expType
      let exp := suspend exp (← read)
      withExtendedEnv exp expType $ check bod type
    | _ =>
      let inferType ← infer term
      if ← equal (← read).lvl type inferType (.sort .zero)
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
      let fncType ← infer fnc
      match fncType with
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
      let domLvl ← isSort dom
      let env ← read
      let dom := suspend dom env
      withExtendedEnv (mkVar name env.lvl dom) dom $ do
        let imgLvl ← isSort img
        let lvl := Univ.reduceIMax domLvl imgLvl
        pure (Value.sort lvl)
    | .letE _ expType exp bod =>
      discard $ isSort expType
      let expType ← eval expType
      check exp expType
      let exp := suspend exp (← read)
      withExtendedEnv exp expType $ infer bod
    | .lit (.num _) => pure $ Value.lty .num
    | .lit (.word _) => pure $ Value.lty .word
    | .lty .. => pure $ Value.sort (Univ.succ Univ.zero)
    | .const name k constUnivs =>
      let univs := (← read).ctx.univs
      let const ← derefConst name k
      withCtx ⟨[], constUnivs.map (Univ.instBulkReduce univs)⟩ $ eval const.type
    | .proj idx expr =>
      let exprType ← infer expr
      match exprType with
      | .app (.const name k univs) params =>
        match ← derefConst name k with
        | .inductive ind => do
          let ctor ← match ind.struct with
            | some ctor => pure ctor
            | none => throw $ .typNotStructure (printVal exprType)
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
            if (← isProp lvl exprType) && !(← isProp lvl typ)
            then throw $ .projEscapesProp (printExpr term)
            else pure typ
          | _ => throw .impossible
        | _ => throw $ .typNotStructure (printVal exprType)
      | _ => throw $ .typNotStructure (printVal exprType)

  partial def isSort (expr : Expr) : TypecheckM Univ := do
    match ← infer expr with
    | .sort u => pure u
    | val => throw $ .notTyp (printVal val)

end

def checkConst : Const → TypecheckM Unit
  | .axiom      struct => discard $ isSort struct.type
  | .theorem    struct
  | .opaque     struct
  | .definition struct => do
    discard $ isSort struct.type
    check struct.value (← eval struct.type)
  -- TODO: check that inductives, constructors and recursors are well-formed
  -- TODO: check that quotient is well-formed. I guess it is possible to do this
  -- while converting from Ipld by checking the cids of the quotient constants
  -- with precomputed ones
  -- TODO: don't we have to do `discard $ isSort struct.type` on every case?
  | _ => pure ()

end Yatima.Typechecker
