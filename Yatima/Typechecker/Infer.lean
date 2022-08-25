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
      dbg_trace s!"\n[check] {term} : {type}"
      let inferType ← infer term
      dbg_trace s!"\n[check] {term} : {type} ⟹   {inferType}"
      if !(← equal (← read).lvl type inferType (.sort .zero))
        then throw $ .valueMismatch (printVal inferType) (printVal type)

  partial def infer (term : Expr) : TypecheckM Value := do
    match term with
    | e@(.var name idx) =>
      dbg_trace s!"\n[infer] .var: {e}"
      let types := (← read).types
      let some type := types.get? idx | throw $ .outOfContextRange name idx types.length
      let ret := type.get
      dbg_trace s!"\n[infer] .var: {e}\n⟹\n{ret}"
      return ret
    | e@(.sort lvl) =>
      dbg_trace s!"\n[infer] .sort: {e}"
      let lvl := Univ.instBulkReduce (← read).ctx.univs lvl.succ
      let ret := Value.sort lvl
      dbg_trace s!"\n[infer] .sort: {e}\n⟹\n{ret}"
      return ret
    | e@(.app fnc arg) =>
      dbg_trace s!"\n[infer] .app: {e}"
      let fncType ← infer fnc
      dbg_trace s!"\n[infer] .app: {e}, {fnc} ↠ {fncType}"
      match fncType with
      | .pi _ _ dom img ctx =>
        check arg dom.get
        let arg := suspend arg (← read)
        let type ← withNewExtendedCtx ctx arg $ eval img
        let ret := type
        dbg_trace s!"\n[infer] .app: {e}\n⟹\n{ret}"
        return ret
      | val => throw $ .notPi (printVal val)
    -- Should we add inference of lambda terms? Perhaps not on this checker,
    -- but on another that is capable of general unification, since this checker
    -- is supposed to be used on fully annotated terms.
    | .lam .. => throw .cannotInferLam
    | e@(.pi name _ dom img) =>
      dbg_trace s!"\n[infer] .pi: {e}"
      let domLvl ← isSort dom
      let env ← read
      let dom := suspend dom env
      withExtendedEnv (mkVar name env.lvl dom) dom $ do
        let imgLvl ← isSort img
        let lvl := Univ.reduceIMax domLvl imgLvl
        let ret := (Value.sort lvl)
        dbg_trace s!"\n[infer] .pi: {e}\n⟹\n{ret}"
        return ret
    | e@(.letE _ expType exp bod) =>
      dbg_trace "\n[infer] .letE: {e}"
      discard $ isSort expType
      let expType ← eval expType
      check exp expType
      let exp := suspend exp (← read)
      let ret ← withExtendedEnv exp expType $ infer bod
      dbg_trace s!"\n[infer] .letE: {e}\n⟹\n{ret}"
      return ret
    | .lit (.num _) => pure $ Value.lty .num
    | .lit (.word _) => pure $ Value.lty .word
    | .lty .. => pure $ Value.sort (Univ.succ Univ.zero)
    | e@(.const name k constUnivs) =>
      dbg_trace "\n[infer] .const: {e}"
      let univs := (← read).ctx.univs
      let const ← derefConst name k
      let ret ← withCtx ⟨[], constUnivs.map (Univ.instBulkReduce univs)⟩ $ eval const.type
      dbg_trace s!"\n[infer] .const: {e}\n⟹\n{ret}"
      return ret
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
