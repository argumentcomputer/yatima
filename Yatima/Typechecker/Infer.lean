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

/-- Reduces the application of a `pi` type to its arguments -/
def applyType : Value → List (SusValue) → TypecheckM Value
  | .pi _ _ _ img imgCtx, arg :: args => do
    let res ← withEnv (imgCtx.extendWith arg) (eval img)
    applyType res args
  | type, [] => pure type
  | _, _ => throw .cannotApply

/-- Checks if a type is an unit inductive -/
def isUnit : Value → TypecheckM Bool
  | .app (.const name i _) _ => do
    match ← derefConst name i with
    | .inductive induct => pure induct.unit
    | _ => pure false
  | _ => pure false

mutual
  /-- 
  Checks if `term : Expr` has type `type : Value`. Returns the expression with flags updated
  -/
  partial def check (term : Expr) (type : Value) : TypecheckM Expr := do
    match term with
    | .lam _ lamName _ _lamDom bod =>
      match type with
      | .pi _ _ dom img env =>
        let lvl := (← read).lvl
        let var : SusValue := mkSusVar sorry lamName lvl
        let img ← withNewExtendedEnv env var $ eval img
        -- TODO check that `lamDom` == `dom`
        -- though this is wasteful, since this would force
        -- `dom`, which might not need to be evaluated.
        withExtendedCtx var dom $ check bod img
      | val => throw $ .notPi (printVal val)
    | .letE _ _ expType exp bod =>
      let (expType, _) ← isSort expType
      let expType ← eval expType
      let _ ← check exp expType
      let exp := suspend exp (← read)
      withExtendedCtx exp (.mk sorry $ .mk fun _ => expType) $ check bod type
    | _ =>
      let (term, inferType) ← infer term
      if !(← equal term.meta.info (← read).lvl type inferType) then
        throw $ .valueMismatch (printVal inferType) (printVal type)
      else
        pure term

  /-- Infers the type of `term : Expr`. Returns the expression with flags updated along with the inferred type  -/
  partial def infer (term : Expr) : TypecheckM (Expr × Value) := do
    match term with
    | .var _ name idx =>
      let types := (← read).types
      let some type := types.get? idx | throw $ .outOfEnvironmentRange name idx types.length
      pure (term, type.get)
    | .sort _ lvl =>
      let lvl := Univ.instBulkReduce (← read).env.univs lvl.succ
      return (term, Value.sort lvl)
    | .app _ fnc arg =>
      let (_, fncType) ← infer fnc
      match fncType with
      | .pi _ _ dom img env =>
        let term ← check arg dom.get
        let arg := suspend arg (← read)
        let typ ← withNewExtendedEnv env arg $ eval img
        pure (term, typ)
      | val => throw $ .notPi (printVal val)
    -- Should we add inference of lambda terms? Perhaps not on this checker,
    -- but on another that is capable of general unification, since this checker
    -- is supposed to be used on fully annotated terms.
    | .lam .. => throw .cannotInferLam
    | .pi _ name _ dom img =>
      let (dom, domLvl) ← isSort dom
      let ctx ← read
      let dom := suspend dom ctx
      withExtendedCtx (mkSusVar sorry name ctx.lvl) dom $ do
        let (img, imgLvl) ← isSort img
        let lvl := Univ.reduceIMax domLvl imgLvl
        return (term, Value.sort lvl)
    | .letE _ _ expType exp bod =>
      let (expType, _) ← isSort expType
      let expType ← eval expType
      let term ← check exp expType
      let exp := suspend exp (← read)
      withExtendedCtx exp (.mk sorry $ .mk fun _ => expType) $ infer bod
    | .lit _ (.natVal _) => pure $ (term, mkConst `Nat (← natIndex) [])
    | .lit _ (.strVal _) => pure $ (term, mkConst `String (← stringIndex) [])
    | .const _ name k constUnivs =>
      let univs := (← read).env.univs
      let const ← derefConst name k
      let typ ← withEnv ⟨[], constUnivs.map (Univ.instBulkReduce univs)⟩ $ eval const.type
      pure (term, typ)
    | .proj _ idx expr =>
      let (expr, exprType) ← infer expr
      match exprType with
      | .app (.const name k univs) params =>
        match ← derefConst name k with
        | .inductive ind => do
          let ctor ← match ind.struct with
            | some ctor => pure ctor
            | none => throw $ .typNotStructure (printVal exprType)
          -- Sanity check TODO: what about ind.indices?
          if ind.params != params.length then throw .impossible else
          let (ctorType, _) ← infer ctor.type
          let mut ctorType ← applyType (← withEnv ⟨[], univs⟩ $ eval ctor.type) params
          for i in [:idx] do
            match ctorType with
            | .pi _ _ _ img piEnv =>
              -- Note: This expression that is generated on the fly is immediately transformed into a value,
              -- which discards the hash, so the value of the hash does not matter here
              let proj := suspend (Expr.proj default i expr) (← read)
              ctorType ← withNewExtendedEnv piEnv proj $ eval img
            | _ => pure ()
          match ctorType with
          | .pi _ _ dom _ _  =>
            let lvl := (← read).lvl
            let typ := dom.get
            -- TODO recover `typ.meta.prop?`
            if expr.meta.info.prop? && !(sorry)
              then throw $ .projEscapesProp (printExpr term)
              else pure (term, typ)
          | _ => throw .impossible
        | _ => throw $ .typNotStructure (printVal exprType)
      | _ => throw $ .typNotStructure (printVal exprType)

  /-- 
  Checks if `expr : Expr` is `Sort lvl` for some level `lvl`, and throws `TypecheckerError.notTyp`
  if it is not.
  -/
  partial def isSort (expr : Expr) : TypecheckM (Expr × Univ) := do
    let (expr, typ) ← infer expr
    match typ with
    | .sort u => pure (expr, u)
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
  withEnv ⟨ [], univs ⟩ $ do
    match c with
    | .theorem    struct
    | .opaque     struct
    | .definition struct => do
      discard $ isSort struct.type
      let type ← eval struct.type
      discard $ check struct.value type
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
