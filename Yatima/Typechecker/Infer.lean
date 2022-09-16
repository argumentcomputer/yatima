import Yatima.Typechecker.Equal

/-!
# Yatima typechecker: Infer

## Basic Structure

This is the third of the three main files that constitute the Yatima typechecker: `Eval`, `Equal`, 
and `Infer`.

TODO: Add a high level overview of Infer in the context of Eval-Equal-Infer.

## Infer

In this module the two major functions `check` and `infer` are defined.
* `check` : Checks that a Yatima expression has a prescribed type.
* `infer` : Determines the type of a given Yatima expression.
-/

namespace Yatima.Typechecker

mutual
  /-- 
  Checks that `term : Expr` has type `type : Value`, and throws `TypecheckError.valueMismatch`
  if it is not.
  -/
  partial def check (term : Expr) (type : Value) : TypecheckM Unit := do
    match term with
    | .lam _ lamName _ _lamDom bod =>
      match type with
      | .pi _ _ dom img ctx =>
        -- TODO check that `lamDom` == `dom`
        -- though this is wasteful, since this would force
        -- `dom`, which might not need to be evaluated.
        let var := mkVar lamName (← read).lvl dom
        let img ← withNewExtendedCtx ctx var $ eval img
        withExtendedEnv var dom $ check bod img
      | val => throw $ .notPi (printVal val)
    | .letE _ _ expType exp bod =>
      discard $ isSort expType
      let expType ← eval expType
      check exp expType
      let exp := suspend exp (← read)
      withExtendedEnv exp expType $ check bod type
    | _ =>
      let inferType ← infer term
      if !(← equal (← read).lvl type inferType (.sort .zero)) then
        throw $ .valueMismatch (printVal inferType) (printVal type)

  /-- Infers the type of `term : Expr` -/
  partial def infer (term : Expr) : TypecheckM Value := do
    match term with
    | .var _ name idx =>
      let types := (← read).types
      let some type := types.get? idx | throw $ .outOfContextRange name idx types.length
      pure type.get
    | .sort _ lvl =>
      let lvl := Univ.instBulkReduce (← read).ctx.univs lvl.succ
      return Value.sort lvl
    | .app _ fnc arg =>
      let fncType ← infer fnc
      match fncType with
      | .pi _ _ dom img ctx =>
        check arg dom.get
        let arg := suspend arg (← read)
        withNewExtendedCtx ctx arg $ eval img
      | val => throw $ .notPi (printVal val)
    -- Should we add inference of lambda terms? Perhaps not on this checker,
    -- but on another that is capable of general unification, since this checker
    -- is supposed to be used on fully annotated terms.
    | .lam .. => throw .cannotInferLam
    | .pi _ name _ dom img =>
      let domLvl ← isSort dom
      let env ← read
      let dom := suspend dom env
      withExtendedEnv (mkVar name env.lvl dom) dom $ do
        let imgLvl ← isSort img
        let lvl := Univ.reduceIMax domLvl imgLvl
        return Value.sort lvl
    | .letE _ _ expType exp bod =>
      discard $ isSort expType
      let expType ← eval expType
      check exp expType
      let exp := suspend exp (← read)
      withExtendedEnv exp expType $ infer bod
    | .lit _ (.num _) => pure $ Value.lty .num
    | .lit _ (.word _) => pure $ Value.lty .word
    | .lty .. => pure $ Value.sort (Univ.succ Univ.zero)
    | .const _ name k constUnivs =>
      let univs := (← read).ctx.univs
      let const ← derefConst name k
      withCtx ⟨[], constUnivs.map (Univ.instBulkReduce univs)⟩ $ eval const.type
    | .proj _ idx expr =>
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
              -- Note: This expression that is generated on the fly is immediately transformed into a value,
              -- which discards the hash, so the value of the hash does not matter here
              let proj := suspend (Expr.proj default i expr) (← read)
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

  /-- 
  Checks if `expr : Expr` is `Sort lvl` for some level `lvl`, and throws `TypecheckerError.notTyp`
  if it is not.
  -/
  partial def isSort (expr : Expr) : TypecheckM Univ := do
    match ← infer expr with
    | .sort u => pure u
    | val => throw $ .notTyp (printVal val)

end

/-- Typechecks a `Yatima.Const`. The `TypecheckM Unit` computation finishes if the check finishes,
otherwise a `TypecheckError` is thrown in some other function in the typechecker stack.

Note that inductives, constructors, and recursors are constructed to typecheck, so this function
only has to check the other `Const` constructors. 
-/
def checkConst (c : Const) : TypecheckM Unit :=
  let univs := c.levels.foldr
    (fun name cont i => Univ.var name i :: (cont (i + 1)))
    (fun _ => []) 0
  withCtx ⟨ [], univs ⟩ $ do
    match c with
    | .theorem    struct
    | .opaque     struct
    | .definition struct => do
      discard $ isSort struct.type
      let type ← eval struct.type
      check struct.value type
    -- TODO: check that inductives, constructors and recursors are well-formed
    -- TODO: check that quotient is well-formed. I guess it is possible to do this
    -- while converting from Ipld by checking the cids of the quotient constants
    -- with precomputed ones
    | .axiom       struct
    | .inductive   struct
    | .constructor struct
    | .extRecursor struct
    | .intRecursor struct
    | .quotient    struct => discard $ isSort struct.type

end Yatima.Typechecker
