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

open TC
open Lurk (F)

def isStruct : Value → TypecheckM (Option (F × Constructor × List Univ × List SusValue))
  | .app (.const k univs) params => do
    match derefConst k (← read).store with
    | .inductiveProj p => do
      let ind ← getIndFromProj p
      match ind.struct with
        | true => do
          let some ctor := ind.ctors.get? 0 
            | throw "Impossible case. Implementation broken."
          -- Sanity check
          if ind.params != params.length then 
            throw "Impossible case. Implementation broken." 
          else
            pure (k, ctor, univs, (params.map (·.1)))
        | false => pure none
    | _ => pure none
  | _ => pure none

/--
  Gives the correct type information for a lambda based on the information of the body.
  No lambdas can be a proposition, a struct or be elements of the unit type.
-/
def lamInfo : SusTypeInfo → SusTypeInfo
| .proof => .proof
| _ => .none

def piInfo : TypeInfo → TypeInfo
| .prop => .prop
| _ => .none

/--
  Gives the correct type information for a term based on its type.
-/
def infoFromType (typ : SusValue) : TypecheckM TypeInfo :=
  match typ.info with
  | .prop => pure .proof
  | _ =>
    match typ.get with
    | .app (.const f _) _ => do match derefConst f (← read).store with
      | .inductiveProj p => 
        let induct ← getIndFromProj p
        if induct.unit then pure .unit else pure .none
      | _ => pure .none
    | .sort lvl => if lvl.isZero then pure .prop else pure .none
    | _ => pure .none

def susInfoFromType (typ : SusValue) : TypecheckM SusTypeInfo :=
  match typ.info with
  | .prop => pure .proof
  | _ =>
    match typ.get with
    | .app (.const f _) _ => do match derefConst f (← read).store with
      | .inductiveProj p =>
        let induct ← getIndFromProj p
        if induct.unit then pure .unit else pure .none
      | _ => pure .none
    | .sort lvl => if lvl.isZero then pure .prop else pure (.sort lvl)
    | _ => pure .none

mutual
  /--
  Checks if `term : Expr` has type `type : SusValue`. Returns the typed IR for `term`
  -/
  partial def check (term : Expr) (type : SusValue) : TypecheckM TypedExpr := do
    dbg_trace s!">> check"
    dbg_trace s!"term: {PP.ppExpr term}"
    dbg_trace s!"type: {type.get}"
    let (term, inferType) ← infer term
    if !(inferType.info == type.info) || !(← equal (← read).lvl type inferType) then
      throw s!"Expected type {type.get}, found type {inferType.get}"
    else
      pure term

  /-- Infers the type of `term : Expr`. Returns the typed IR for `term` along with its inferred type  -/
  partial def infer (term : Expr) : TypecheckM (TypedExpr × SusValue) := do
    match term with
    | .var idx lvls =>
      dbg_trace s!">> infer var@{idx}"
      if idx < (← read).lvl then
        dbg_trace s!"bound"
        -- this is a bound free variable
        if !lvls.isEmpty then
          -- bound free variables should never have universe levels (sanity check)
          throw s!"found var@{idx} with unexpected universe variables"
        let types := (← read).types
        let some type := types.get? idx
          | throw s!"var@{idx} out of environment range (size {types.length})"
        let term := .var (← susInfoFromType type) idx
        dbg_trace s!"term: {term}"
        dbg_trace s!"type: {type.get}"
        pure (term, type)
      else
        -- this free variable came from `recrCtx`, and thus represents a mutual reference
        match (← read).mutTypes.find? (idx - (← read).lvl) with
        | some (constF, typeValFn) =>
          let type := typeValFn lvls
          let term := .const (← susInfoFromType type) constF lvls
          pure (term, type)
        | none =>
          dbg_trace s!">> infer term:\n  {reprStr term}"
          throw $ s!"var@{idx} out of environment range (size {(← read).types.length})" 
            ++ " and does not represent a mutual constant"
    | .sort lvl =>
      dbg_trace s!">> infer sort"
      let univs := (← read).env.univs
      let lvl := Univ.instBulkReduce univs lvl
      let lvl' := Univ.succ lvl
      let typ := .mk .none ⟨ fun _ => .sort lvl' ⟩
      -- NOTE: we populate `SusTypeInfo.sort` here for consistency but technically it isn't necessary
      -- because `lvl'` can never become `Univ.zero`.
      return (.sort (.sort lvl') lvl, typ)
    | .app fnc arg =>
      dbg_trace s!">> infer app"
      dbg_trace s!"fnc: {PP.ppExpr fnc}"
      dbg_trace s!"app: {PP.ppExpr arg}"
      let (fnc, fncType) ← infer fnc
      dbg_trace s!"fncType: {fncType.get}"
      match fncType.get with
      | .pi dom img env =>
        dbg_trace s!"do a check 1"
        let arg ← check arg dom
        let typ := suspend img { ← read with env := env.extendWith $ suspend arg (← read) (← get)} (← get)
        let term := .app (← susInfoFromType typ) fnc arg
        pure (term, typ)
      | val => throw s!"Expected a pi type, found '{val}'"
    | .lam dom bod => do
      dbg_trace s!">> infer lam"
      let (dom, _) ← isSort dom
      let ctx ← read
      let domVal := suspend dom ctx (← get)
      let var := mkSusVar (← infoFromType domVal) ctx.lvl
      let (bod, img) ← withExtendedCtx var domVal $ infer bod
      let term := .lam (lamInfo bod.info) dom bod
      let typ := .mk (piInfo img.info) $
        Value.pi domVal (← quote (ctx.lvl+1) img.info.toSus ctx.env img.get) ctx.env
      pure (term, typ)
    | .pi dom img =>
      dbg_trace s!">> infer pi"
      dbg_trace s!"dom: {PP.ppExpr dom}"
      dbg_trace s!"img: {PP.ppExpr img}"
      let (dom, domLvl) ← isSort dom
      let ctx ← read
      let domVal := suspend dom ctx (← get)
      let domSusVal := mkSusVar (← infoFromType domVal) ctx.lvl
      dbg_trace s!"domVal: {domVal.get}"
      withExtendedCtx domSusVal domVal $ do
        let (img, imgLvl) ← isSort img
        let typ := .mk .none ⟨ fun _ => .sort $ .reduceIMax domLvl imgLvl ⟩
        let term := .pi (← susInfoFromType typ) dom img
        return (term, typ)
    | .letE expType exp bod =>
      dbg_trace s!">> infer let"
      let (expType, _) ← isSort expType
      let expTypeVal := suspend expType (← read) (← get)
      dbg_trace s!"do a check 2"
      let exp ← check exp expTypeVal
      let expVal := suspend exp (← read) (← get)
      let (bod, typ) ← withExtendedCtx expVal expTypeVal $ infer bod
      let term := .letE bod.info expType exp bod
      return (term, typ)
    | .lit (.natVal v) =>
      let typ := .mk .none (mkConst (← primF .nat) [])
      pure $ (.lit .none (.natVal v), typ)
    | .lit (.strVal s) =>
      let typ := .mk .none (mkConst (← primF .string) [])
      pure $ (.lit .none (.strVal s), typ)
    | .const k constUnivs =>
      dbg_trace s!">> infer const {k}"
      let univs := (← read).env.univs
      checkConst k
      let tconst ← derefTypedConst k
      let env := ⟨[], constUnivs.map (Univ.instBulkReduce univs)⟩
      let typ := suspend tconst.type { ← read with env := env } (← get)
      pure (.const (← susInfoFromType typ) k constUnivs, typ)
    | .proj idx expr =>
      dbg_trace s!">> infer proj"
      let (expr, exprType) ← infer expr
      let some (ind, ctor, univs, params) ← isStruct exprType.get
        | throw s!"Expected a structure type, found {exprType.get}"
      -- annotate constructor type
      let (ctorType, _) ← infer ctor.type
      let mut ctorType ← applyType (← withEnv ⟨[], univs⟩ $ eval ctorType) params.reverse
      for i in [:idx] do
        match ctorType with
        | .pi dom img piEnv =>
          let info ← susInfoFromType dom
          let proj := suspend (.proj info ind i expr) (← read) (← get)
          ctorType ← withNewExtendedEnv piEnv proj $ eval img
        | _ => pure ()
      match ctorType with
      | .pi dom _ _  =>
        match exprType.info, dom.info with
        | .prop, .prop =>
          let term := .proj (← susInfoFromType dom) ind idx expr
          pure (term, dom)
        | .prop, _ =>
          throw s!"Projection {expr}.{idx} not allowed"
        | _, _ =>
          let term := .proj (← susInfoFromType dom) ind idx expr
          pure (term, dom)
      | _ => throw "Impossible case. Implementation broken."

  /--
  Checks if `expr : Expr` is `Sort lvl` for some level `lvl`, and throws `TypecheckerError.notTyp`
  if it is not.
  -/
  partial def isSort (expr : Expr) : TypecheckM (TypedExpr × Univ) := do
    dbg_trace s!">> isSort"
    dbg_trace s!"expr: {PP.ppExpr expr}"
    let (expr, typ) ← infer expr
    match typ.get with
    | .sort u =>
      dbg_trace s!">> isSort res expr: {expr} and {PP.ppUniv u}"
      pure (expr, u)
    | val => throw s!"Expected a sort type, found '{val}'"

  partial def buildMutTypes (indBlockF : F) : TypecheckM RecrCtx := do
    dbg_trace s!">> buildMutTypes"
    let quick := (← read).quick 
    let indBlock ← match derefConst indBlockF (← read).store with
      | .mutIndBlock blk => pure blk
      | _ => throw "Invalid Const kind. Expected mutIndBlock"
    let mut indTypes : List (F × Expr) := []
    let mut ctorTypes : List (F × Expr) := []
    let mut recTypes : List (F × Expr) := []
    for (indIdx, ind) in indBlock.enum do
      indTypes := indTypes ++ [(mkInductiveProjF indBlockF indIdx quick, ind.type)]
      ctorTypes := ctorTypes ++ (← ind.ctors.enum.mapM fun (cidx, ctor) => do pure (mkConstructorProjF indBlockF indIdx cidx quick, ctor.type))
      recTypes := recTypes.append (← ind.recrs.enum.mapM fun (ridx, recr) => do pure (mkRecursorProjF indBlockF indIdx ridx quick, recr.type))
    -- TODO check order (should be same as `recrCtx` in CA)
    let mutTypes ← (indTypes ++ ctorTypes ++ recTypes).enum.foldlM (init := default) fun acc (i, projF, type) => do
      -- FIXME repeated computation (this will happen again when we
      -- actually check the recursor on its own)
      dbg_trace s!"try building type:\n{PP.ppExpr type}"
      let (type, _) ← withMutTypes acc $ isSort type
      let ctx ← read
      let stt ← get
      let typeSus := (suspend type {ctx with env := .mk ctx.env.exprs ·} stt)
      pure $ acc.insert i (projF, typeSus)
    pure mutTypes

  /-- Typechecks a `Yatima.Const`. The `TypecheckM Unit` computation finishes if the check finishes,
  otherwise a `TypecheckError` is thrown in some other function in the typechecker stack.

  Note that inductives, constructors, and recursors are constructed to typecheck, so this function
  only has to check the other `Const` constructors.
  -/
  partial def checkConst (f : F) : TypecheckM Unit := withResetCtx do
    dbg_trace s!">> checkConst"
    match (← get).typedConsts.find? f with
    | some _ => pure ()
    | none =>
      let c := derefConst f (← read).store
      if c.isMutType then
        return ()
      dbg_trace s!"{PP.ppConst c}"
      let univs := List.range (← c.levels) |>.map .var
      dbg_trace s!"checkConst with univs: {univs.map PP.ppUniv}"
      withEnv ⟨ [], univs ⟩ do
        let quick := (← read).quick
        let newConst ← match c with
          | .axiom ax    => 
            dbg_trace s!">> checkConst axiom"
            let (type, _) ← isSort ax.type
            pure $ TypedConst.axiom type
          | .opaque data =>
            dbg_trace s!">> checkConst opaque"
            let (type, _) ← isSort data.type
            let typeSus := suspend type (← read) (← get)
            dbg_trace s!"do a check 3"
            let value ← check data.value typeSus
            pure $ TypedConst.opaque type value
          | .theorem data =>
            dbg_trace s!">> checkConst theorem"
            let (type, _) ← isSort data.type
            let typeSus := suspend type (← read) (← get)
            dbg_trace s!"do a check 4"
            let value ← check data.value typeSus
            pure $ TypedConst.theorem type value
          | .definition data =>
            dbg_trace s!">> checkConst definition"
            let (type, _) ← isSort data.type
            let typeSus := suspend type (← read) (← get)
            let value ← match data.safety with
              | .partial =>
                let mut mutTypes := default
                mutTypes ← do
                  -- TODO avoid repeated work here
                  let (type, _) ← isSort data.type
                  let ctx ← read
                  let typeSus := (suspend type {ctx with env := .mk ctx.env.exprs ·} (← get))
                  pure $ mutTypes.insert 0 (f, typeSus)
                dbg_trace s!"do a check 5"
                withMutTypes mutTypes $ check data.value typeSus
              | _ => 
                dbg_trace s!"do a check 6"
                check data.value typeSus
            pure $ TypedConst.definition type value data.safety
          | .definitionProj p@⟨defBlockF, _⟩ =>
            dbg_trace s!">> checkConst definition proj"
            let data ← getDefFromProj p
            let (type, _) ← isSort data.type
            let defBlock ← match derefConst defBlockF (← read).store with
              | .mutDefBlock blk => pure blk
              | _ => throw "Invalid Const kind. Expected mutDefBlock"
            let typeSus := suspend type (← read) (← get)
            let value ← match data.safety with
              | .partial =>
                -- TODO check order (should be same as `recrCtx` in CA)
                let mutTypes ← defBlock.enum.foldlM (init := default) fun acc (i, defn) => do
                  let defProjF := mkDefinitionProjF defBlockF i quick
                  -- TODO avoid repeated work here
                  let (type, _) ← isSort defn.type
                  let ctx ← read
                  let typeSus := (suspend type {ctx with env := .mk ctx.env.exprs ·} (← get))
                  pure $ acc.insert i (defProjF, typeSus)
                withMutTypes mutTypes $ check data.value typeSus
              | _ => check data.value typeSus
            pure $ TypedConst.definition type value data.safety
          | .inductiveProj p@⟨indBlockF, _⟩ =>
            dbg_trace s!">> checkConst inductive proj"
            let data ← getIndFromProj p
            dbg_trace s!"data:\n{PP.ppInductive data}"
            let mutTypes ← buildMutTypes indBlockF
            dbg_trace s!"bad type:\n{PP.ppExpr data.type}"
            let (type, _) ← withMutTypes mutTypes $ isSort data.type
            pure $ .inductive type data.struct
          | .constructorProj p@⟨indBlockF, _, _⟩ =>
            dbg_trace s!">> checkConst constructor proj"
            let data ← getCtorFromProj p
            dbg_trace s!"data:\n{PP.ppConstructor data}"
            let mutTypes ← buildMutTypes indBlockF
            let (type, _) ← withMutTypes mutTypes $ isSort data.type
            pure $ .constructor type data.idx data.fields
          | .recursorProj p@⟨indBlockF, idx, _⟩ => do
            dbg_trace s!">> checkConst recursor proj"
            let data ← getRecrFromProj p
            dbg_trace s!"data:\n{PP.ppRecursor data}"
            let mutTypes ← buildMutTypes indBlockF
            let rules ← data.rules.mapM fun rule => do
              let (rhs, _) ← withMutTypes mutTypes $ infer rule.rhs
              pure (rule.fields, rhs)
            let (type, _) ← withMutTypes mutTypes $ isSort (← c.type)
            pure $ .recursor type data.params data.motives data.minors
              data.indices data.isK ⟨indBlockF, idx⟩ rules
          | .quotient data => 
            dbg_trace s!">> checkConst quotient"
            let (type, _) ← isSort (← c.type)
            pure $ .quotient type data.kind
          | _ => throw "Impossible case. Cannot typecheck a mutual block."
        -- TODO is it okay to use the original hash for the `TypedConst`, or should we compute a new one?
        modify fun stt => { stt with typedConsts := stt.typedConsts.insert f newConst }
end

end Yatima.Typechecker
