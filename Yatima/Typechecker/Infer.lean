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

open IR PP
open Lurk (F)

/--
  Gives the correct type information for a lambda based on the information of the body.
  No lambdas can be a proposition, a struct or be elements of the unit type.
-/
def lamInfo : TypeInfo → TypeInfo
| .proof => .proof
| _ => .none

def piInfo (dom img : TypeInfo) : TypecheckM TypeInfo := match dom, img with
| .sort lvl, .sort lvl' => pure $ .sort $ .reduceIMax lvl lvl'
| .sort _, _ => throw "Image is not a type"
| _, .sort _ => throw "Domain is not a type"
| _, _ => throw "Neither image nor domain are types"

def eqSortInfo (inferType expectType : TypedValue) : TypecheckM Bool := do
  match inferType.info, expectType.info with
  | .sort lvl, .sort lvl' => pure $ lvl.equalUniv lvl'
  | .sort _, e => throw s!"Expected type {← ppValue expectType.body} {repr e} is not actually a type"
  | e, .sort _ => throw s!"Inferred type {← ppValue inferType.body} {repr e} is not actually a type"
  | e, e' => throw s!"Neither expected {← ppValue expectType.body} {repr e} nor inferred types {← ppValue inferType.body} {repr e'} are actually types"
/--
  Gives the correct type information for a term based on its type.
-/
def infoFromType (typ : TypedValue) : TypecheckM TypeInfo :=
  match typ.info with
  | .sort .zero => pure .proof
  | _ =>
    match typ.body with
    | .app (.const f _) _ _ => do match derefConst f (← read).store with
      | .inductiveProj p =>
        let induct ← getIndFromProj p
        if induct.unit then pure .unit else pure .none
      | _ => pure .none
    | .sort lvl => pure (.sort lvl)
    | _ => pure .none

mutual

  partial def getStructInfo (v : Value) :
      TypecheckM (F × TypedExpr × List Univ × List TypedValue) := do
    match v with
    | .app (.const indF univs) params _ =>
      let .inductiveProj p := derefConst indF (← read).store 
        | throw s!"Expected a structure type, found {← ppValue v}"
      let ind ← getIndFromProj p
      -- Sanity check
      unless ind.struct && ind.params == params.length do
        throw s!"Expected a structure type, found {← ppValue v}"
      withLimitedAxioms $ checkConst indF
      let ctorF := mkConstructorProjF p.block p.idx 0 (← read).quick
      match (← get).typedConsts.find? ctorF with
      | .some (.constructor type _ _) =>
        return (indF, type, univs, params)
      | _ => throw s!"Implementation broken: ctorF {ctorF} is not a constructor"
    | v => throw s!"Expected a structure type, found {← ppValue v}"

  /--
  Checks if `term : IR.Expr` has type `type : TypedValue`. Returns the typed IR for `term`
  -/
  partial def check (term : IR.Expr) (type : TypedValue) : TypecheckM TypedExpr := do
    let (term, inferType) ← infer term
    if !(← eqSortInfo inferType type) then
      throw s!"Term: {← ppTypedExpr term}\nInfo mismatch:\n{repr inferType.info}\n\nnot equal to\n{repr type.info}\n\nExpected type: {← ppValue type.body}\nInferred type: {← ppValue inferType.body}"
    if !(← equal (← read).lvl type inferType) then
      throw s!"Expected type {← ppValue type.body}, found type {← ppValue inferType.body}"
    pure term

  /-- Infers the type of `term : IR.Expr`. Returns the typed IR for `term` along with its inferred type  -/
  partial def infer (term : IR.Expr) : TypecheckM (TypedExpr × TypedValue) := do
    match term with
    | .var idx lvls =>
      let ctx ← read
      if idx < ctx.lvl then
        -- this is a bound free variable
        if !lvls.isEmpty then
          -- bound free variables should never have universe levels (sanity check)
          throw s!"found var@{idx} with unexpected universe variables"
        let types := ctx.types
        let some type := types.get? idx
          | throw s!"var@{idx} out of environment range (size {types.length})"
        let term := ⟨← infoFromType type, .var idx⟩
        pure (term, type)
      else
        -- this free variable came from `recrCtx`, and thus represents a mutual reference
        match ctx.mutTypes.find? (idx - ctx.lvl) with
        | some (constF, exprs, type) =>
          if some constF == ctx.recF? then
            throw s!"Invalid recursion in {(← read).constNames.getF constF}"
          let typeVal ← withEnv ⟨exprs, lvls⟩ $ evalTyped type
          let term := ⟨← infoFromType typeVal, .const constF lvls⟩
          pure (term, typeVal)
        | none =>
          throw $ s!"var@{idx} out of environment range (size {ctx.types.length})"
            ++ " and does not represent a mutual constant"
    | .sort lvl =>
      let univs := (← read).env.univs
      let lvl := Univ.instBulkReduce univs lvl
      let lvl' := lvl.succ
      let typ := .mk (.sort lvl'.succ) (.sort lvl')
      -- NOTE: we populate `SusTypeInfo.sort` here for consistency but technically it isn't necessary
      -- because `lvl'` can never become `Univ.zero`.
      let term := ⟨.sort lvl', .sort lvl⟩
      return (term, typ)
    | .app fnc' arg =>
      let (fnc, fncType) ← infer fnc'
      match fncType.body with
      | .pi dom img env =>
        let arg ← check arg dom
        let argVal ← evalTyped arg
        let typ ← withNewExtendedEnv env argVal $ evalTyped img
        let term := ⟨← infoFromType typ, .app fnc arg⟩
        pure (term, typ)
      | val => throw s!"Expected a pi type, found {← ppValue val}"
    | .lam dom bod => do
      let (dom, _) ← isSort dom
      let ctx ← read
      let domVal ← evalTyped dom
      let var := mkVar (← infoFromType domVal) ctx.lvl
      let (bod, imgVal) ← withExtendedCtx var domVal $ infer bod
      let term := ⟨lamInfo bod.info, .lam dom bod⟩
      let typ := .mk (← piInfo domVal.info imgVal.info) $
        Value.pi domVal (← quoteTyped (ctx.lvl+1) ctx.env imgVal) ctx.env
      pure (term, typ)
    | .pi dom img =>
      let (dom, domLvl) ← isSort dom
      let ctx ← read
      let domVal ← evalTyped dom
      let domSusVal := mkVar (← infoFromType domVal) ctx.lvl
      withExtendedCtx domSusVal domVal $ do
        let (img, imgLvl) ← isSort img
        let sortLvl := .reduceIMax domLvl imgLvl
        let typ := .mk (.sort sortLvl.succ) (.sort $ sortLvl)
        let term := ⟨← infoFromType typ, .pi dom img⟩
        return (term, typ)
    | .letE expType exp bod =>
      let (expType, _) ← isSort expType
      let expTypeVal ← evalTyped expType
      let exp ← check exp expTypeVal
      let expVal ← evalTyped exp
      let (bod, typ) ← withExtendedCtx expVal expTypeVal $ infer bod
      let term := ⟨bod.info, .letE expType exp bod⟩
      return (term, typ)
    | .lit (.natVal v) =>
      let typ := .mk (.sort $ .succ .zero) (mkConst (← primF .nat) [])
      let term := ⟨.none, .lit (.natVal v)⟩
      pure $ (term, typ)
    | .lit (.strVal s) =>
      let typ := .mk (.sort $ .succ .zero) (mkConst (← primF .string) [])
      let term := ⟨.none, .lit (.strVal s)⟩
      pure $ (term, typ)
    | .const k constUnivs =>
      withLimitedAxioms $ checkConst k
      let ctx ← read
      let univs := ctx.env.univs
      let tconst ← derefTypedConst k
      let env := ⟨[], constUnivs.map (Univ.instBulkReduce univs)⟩
      let typ ← withEnv env $ evalTyped tconst.type
      let term := ⟨← infoFromType typ, .const k constUnivs⟩
      pure (term, typ)
    | .proj idx expr =>
      let (expr, exprType) ← infer expr
      let (indF, ctorType, univs, params) ←  getStructInfo exprType.body
      let mut ctorType ← applyType (← withEnv ⟨[], univs⟩ $ eval ctorType) params.reverse
      for i in [:idx] do
        match ctorType with
        | .pi dom img piEnv =>
          let info ← infoFromType dom
          let proj ← evalTyped ⟨info, .proj indF i expr⟩
          ctorType ← withNewExtendedEnv piEnv proj $ eval img
        | _ => pure ()
      match ctorType with
      | .pi dom _ _  =>
        match exprType.info, dom.info with
        | .sort .zero, .sort .zero =>
          let term := ⟨← infoFromType dom, .proj indF idx expr⟩
          pure (term, dom)
        | .sort .zero, _ =>
          throw s!"Projection {← ppTypedExpr expr}.{idx} not allowed"
        | _, _ =>
          let term := ⟨← infoFromType dom, .proj indF idx expr⟩
          pure (term, dom)
      | _ => throw "Impossible case. Implementation broken."

  /--
  Checks if `expr : IR.Expr` is `Sort lvl` for some level `lvl`, and throws `TypecheckerError.notTyp`
  if it is not.
  -/
  partial def isSort (expr : IR.Expr) : TypecheckM (TypedExpr × Univ) := do
    let (expr, typ) ← infer expr
    match typ.body with
    | .sort u =>
      pure (expr, u)
    | val => throw s!"Expected a sort type, found {← ppValue val}"

  partial def checkIndBlock (indBlockF : F) : TypecheckM Unit := do
    let quick := (← read).quick
    let indBlock ← match derefConst indBlockF (← read).store with
      | .mutIndBlock blk => pure blk
      | _ => throw "Invalid Const kind. Expected mutIndBlock"

    -- Check all inductives
    let mut mutTypes : RecrCtx := .empty
    for (indIdx, ind) in indBlock.enum do
      let f := mkInductiveProjF indBlockF indIdx quick
      let univs := List.range ind.lvls |>.map .var
      let (type, _) ← withEnv ⟨ [], univs ⟩ $ isSort ind.type
      let ctx ← read
      mutTypes := mutTypes.insert indIdx (f, ctx.env.exprs, type)
      modify fun stt => { stt with typedConsts := stt.typedConsts.insert f (.inductive type ind.struct) }

    -- Check all constructors
    for (indIdx, ind) in indBlock.enum do
      let start := mutTypes.size
      for (cidx, ctor) in ind.ctors.enum do
        let f := mkConstructorProjF indBlockF indIdx cidx quick
        let univs := List.range ctor.lvls |>.map .var
        let (type, _) ← withEnv ⟨ [], univs ⟩ $ withMutTypes mutTypes $ isSort ctor.type
        let ctx ← read
        mutTypes := mutTypes.insert (start + cidx) (f, ctx.env.exprs, type)
        modify fun stt => { stt with typedConsts := stt.typedConsts.insert f (.constructor type ctor.idx ctor.fields) }

    -- Check all recursor types
    for (indIdx, ind) in indBlock.enum do
      let start := mutTypes.size
      for (ridx, recr) in ind.recrs.enum do
        let f := mkRecursorProjF indBlockF indIdx ridx quick
        let univs := List.range recr.lvls |>.map .var
        let (type, _) ← withEnv ⟨ [], univs ⟩ $ withMutTypes mutTypes $ isSort recr.type
        let ctx ← read
        mutTypes := mutTypes.insert (start + ridx) (f, ctx.env.exprs, type)

    -- Check all recursor rules
    for (indIdx, ind) in indBlock.enum do
      for (ridx, recr) in ind.recrs.enum do
        -- TODO: do not recompute `f`, `univs` and `type`
        let f := mkRecursorProjF indBlockF indIdx ridx quick
        let univs := List.range recr.lvls |>.map .var
        let (type, _) ← withEnv ⟨ [], univs ⟩ $ withMutTypes mutTypes $ isSort recr.type
        let indProj := ⟨indBlockF, indIdx⟩
        let rules ← recr.rules.mapM fun rule => do
          let (rhs, _) ← withEnv ⟨ [], univs ⟩ $ withMutTypes mutTypes $ infer rule.rhs
          pure (rule.fields, rhs)
        let recrConst := .recursor type recr.params recr.motives recr.minors recr.indices recr.isK indProj ⟨rules⟩
        modify fun stt => { stt with typedConsts := stt.typedConsts.insert f recrConst }

    return ()

  /-- Typechecks a `Yatima.Const`. The `TypecheckM Unit` computation finishes if the check finishes,
  otherwise a `TypecheckError` is thrown in some other function in the typechecker stack.

  Note that inductives, constructors, and recursors are constructed to typecheck, so this function
  only has to check the other `Const` constructors.
  -/
  partial def checkConst (f : F) : TypecheckM Unit := withResetCtx do
    match (← get).typedConsts.find? f with
    | some _ =>
      pure ()
    | none =>
      let c := derefConst f (← read).store
      if c.isMutType then return ()
      let univs := List.range (← c.levels) |>.map .var
      withEnv ⟨ [], univs ⟩ do
        let quick := (← read).quick
        let newConst ← match c with
          | .axiom ax =>
            if (← read).limitAxioms then
              if quick then
                if !(allowedAxiomQuick f) then
                  throw s!"Axiom {(← read).constNames.getF f} is not allowed"
              else
                if !(allowedAxiom f) then
                  throw s!"Axiom {(← read).constNames.getF f} is not allowed"
            let (type, _) ← isSort ax.type
            pure $ TypedConst.axiom type
          | .opaque data =>
            let (type, _) ← isSort data.type
            let typeVal ← evalTyped type
            let value ← withRecF f $ check data.value typeVal
            pure $ TypedConst.opaque type value
          | .theorem data =>
            let (type, _) ← isSort data.type
            let typeVal ← evalTyped type
            let value ← withRecF f $ check data.value typeVal
            pure $ TypedConst.theorem type value
          | .definition data =>
            let (type, _) ← isSort data.type
            let ctx ← read
            let typeVal ← evalTyped type
            let value ←
              if data.part then
                let mutTypes :=
                  (default : RecrCtx).insert 0 (f, ctx.env.exprs, type)
                withMutTypes mutTypes $ withRecF f $ check data.value typeVal
              else withRecF f $ check data.value typeVal
            pure $ TypedConst.definition type value data.part
          | .definitionProj p@⟨defBlockF, _⟩ =>
            let data ← getDefFromProj p
            let (type, _) ← isSort data.type
            let ctx ← read
            let defBlock ← match derefConst defBlockF ctx.store with
              | .mutDefBlock blk => pure blk
              | _ => throw "Invalid Const kind. Expected mutDefBlock"
            let typeVal ← evalTyped type
            let value ←
              if data.part then
                -- check order should be the same as `recrCtx` in CA
                let mutTypes ← defBlock.enum.foldlM (init := default) fun acc (i, defn) => do
                  let defProjF := mkDefinitionProjF defBlockF i quick
                  -- TODO avoid repeated work here
                  let (type, _) ← isSort defn.type
                  pure $ acc.insert i (defProjF, ctx.env.exprs, type)
                withMutTypes mutTypes $ withRecF f $ check data.value typeVal
              else withRecF f $ check data.value typeVal
            pure $ TypedConst.definition type value data.part
          | .inductiveProj ⟨indBlockF, _⟩ =>
            checkIndBlock indBlockF
            return ()
          | .constructorProj ⟨indBlockF, _, _⟩ =>
            checkIndBlock indBlockF
            return ()
          | .recursorProj ⟨indBlockF, _, _⟩ =>
            checkIndBlock indBlockF
            return ()
          | .quotient data =>
            let (type, _) ← isSort (← c.type)
            pure $ .quotient type data.kind
          | _ => throw "Impossible case. Cannot typecheck a mutual block."
        -- TODO is it okay to use the original hash for the `TypedConst`, or should we compute a new one?
        modify fun stt => { stt with typedConsts := stt.typedConsts.insert f newConst }
end

end Yatima.Typechecker
