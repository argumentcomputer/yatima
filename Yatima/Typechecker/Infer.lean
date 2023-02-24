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

  partial def getStructInfo (v : Value) : 
      TypecheckM (F × TypedExpr × List Univ × List SusValue) := do
    let err := s!"Expected a structure type, found {← ppValue v}"
    match v with
    | .app (.const indF univs) params => do
      let .inductiveProj p := derefConst indF (← read).store | throw err
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
  Checks if `term : Expr` has type `type : SusValue`. Returns the typed IR for `term`
  -/
  partial def check (term : Expr) (type : SusValue) : TypecheckM TypedExpr := do
    -- dbg_trace s!">> check"
    -- dbg_trace s!"term: {PP.ppExpr term}"
    -- dbg_trace s!"type: {type.get}"
    let (term, inferType) ← infer term
    -- dbg_trace s!">> check just inferred: {term}"
    if !(inferType.info == type.info) || !(← equal (← read).lvl type inferType) then
      -- dbg_trace s!"{← ppTypecheckCtx}"
      throw s!"Expected type {← ppValue type.get}, found type {← ppValue inferType.get}"
    pure term

  /-- Infers the type of `term : Expr`. Returns the typed IR for `term` along with its inferred type  -/
  partial def infer (term : Expr) : TypecheckM (TypedExpr × SusValue) := do
    -- dbg_trace ">> infer {← ppExpr term}"
    match term with
    | .var idx lvls =>
      let ctx ← read
      -- dbg_trace s!">> infer var@{idx}"
      if idx < ctx.lvl then
        -- dbg_trace s!"bound"
        -- this is a bound free variable
        if !lvls.isEmpty then
          -- bound free variables should never have universe levels (sanity check)
          throw s!"found var@{idx} with unexpected universe variables"
        let types := ctx.types
        let some type := types.get? idx
          | throw s!"var@{idx} out of environment range (size {types.length})"
        let term := .var (← susInfoFromType type) idx
        -- dbg_trace s!"term: {term}"
        -- dbg_trace s!"type: {type.get}"
        pure (term, type)
      else
        -- this free variable came from `recrCtx`, and thus represents a mutual reference
        match ctx.mutTypes.find? (idx - ctx.lvl) with
        | some (constF, typeValFn) =>
          if some constF == ctx.recF? then
            throw s!"Invalid recursion in {(← read).constNames.getF constF}"
          let type := typeValFn lvls
          let term := .const (← susInfoFromType type) constF lvls
          pure (term, type)
        | none =>
          -- dbg_trace s!">> infer term:\n  {reprStr term}"
          throw $ s!"var@{idx} out of environment range (size {ctx.types.length})" 
            ++ " and does not represent a mutual constant"
    | .sort lvl =>
      -- dbg_trace s!">> infer sort"
      let univs := (← read).env.univs
      let lvl := Univ.instBulkReduce univs lvl
      let lvl' := Univ.succ lvl
      let typ := .mk .none ⟨ fun _ => .sort lvl' ⟩
      -- NOTE: we populate `SusTypeInfo.sort` here for consistency but technically it isn't necessary
      -- because `lvl'` can never become `Univ.zero`.
      return (.sort (.sort lvl') lvl, typ)
    | .app fnc arg =>
      -- dbg_trace s!">> infer app"
      -- dbg_trace s!"fnc: {PP.ppExpr fnc}"
      -- dbg_trace s!"app: {PP.ppExpr arg}"
      let (fnc, fncType) ← infer fnc
      -- dbg_trace s!"fncType: {fncType.get}"
      match fncType.get with
      | .pi dom img env =>
        -- dbg_trace s!"do a check 1"
        let arg ← check arg dom
        let ctx ← read
        let stt ← get
        let typ := suspend img { ctx with env := env.extendWith $ suspend arg ctx stt} stt
        let term := .app (← susInfoFromType typ) fnc arg
        pure (term, typ)
      | val => throw s!"Expected a pi type, found {← ppValue val}"
    | .lam dom bod => do
      -- dbg_trace s!">> infer lam"
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
      -- dbg_trace s!">> infer pi"
      -- dbg_trace s!"dom: {PP.ppExpr dom}"
      -- dbg_trace s!"img: {PP.ppExpr img}"
      let (dom, domLvl) ← isSort dom
      let ctx ← read
      let domVal := suspend dom ctx (← get)
      let domSusVal := mkSusVar (← infoFromType domVal) ctx.lvl
      -- dbg_trace s!"domVal: {domVal.get}"
      withExtendedCtx domSusVal domVal $ do
        let (img, imgLvl) ← isSort img
        let typ := .mk .none ⟨ fun _ => .sort $ .reduceIMax domLvl imgLvl ⟩
        let term := .pi (← susInfoFromType typ) dom img
        return (term, typ)
    | .letE expType exp bod =>
      -- dbg_trace s!">> infer let"
      let (expType, _) ← isSort expType
      let ctx ← read
      let expTypeVal := suspend expType ctx (← get)
      -- dbg_trace s!"do a check 2"
      let exp ← check exp expTypeVal
      let expVal := suspend exp ctx (← get)
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
      -- dbg_trace s!">> infer const {getF k}"
      withLimitedAxioms $ checkConst k
      let ctx ← read
      let univs := ctx.env.univs
      let tconst ← derefTypedConst k
      let env := ⟨[], constUnivs.map (Univ.instBulkReduce univs)⟩
      let typ := suspend tconst.type { ctx with env := env } (← get)
      pure (.const (← susInfoFromType typ) k constUnivs, typ)
    | .proj idx expr =>
      -- dbg_trace s!">> infer proj"
      let (expr, exprType) ← infer expr
      let (indF, ctorType, univs, params) ←  getStructInfo exprType.get
      -- dbg_trace s!"3. ctorType:\n{ctorType}"
      let mut ctorType ← applyType (← withEnv ⟨[], univs⟩ $ eval ctorType) params.reverse
      for i in [:idx] do
        -- dbg_trace s!"iter {i}. ctorType:\n{ctorType}"
        match ctorType with
        | .pi dom img piEnv =>
          let info ← susInfoFromType dom
          let proj := suspend (.proj info indF i expr) (← read) (← get)
          ctorType ← withNewExtendedEnv piEnv proj $ eval img
        | _ => pure ()
      -- dbg_trace s!">> infer proj end"
      match ctorType with
      | .pi dom _ _  =>
        match exprType.info, dom.info with
        | .prop, .prop =>
          let term := .proj (← susInfoFromType dom) indF idx expr
          pure (term, dom)
        | .prop, _ =>
          throw s!"Projection {← ppTypedExpr expr}.{idx} not allowed"
        | _, _ =>
          let term := .proj (← susInfoFromType dom) indF idx expr
          pure (term, dom)
      | _ => throw "Impossible case. Implementation broken."

  /--
  Checks if `expr : Expr` is `Sort lvl` for some level `lvl`, and throws `TypecheckerError.notTyp`
  if it is not.
  -/
  partial def isSort (expr : Expr) : TypecheckM (TypedExpr × Univ) := do
    -- dbg_trace s!">> isSort"
    -- dbg_trace s!"expr: {PP.ppExpr expr}"
    let (expr, typ) ← infer expr
    match typ.get with
    | .sort u =>
      -- dbg_trace s!">> isSort res expr: {expr} and {PP.ppUniv u}"
      pure (expr, u)
    | val => throw s!"Expected a sort type, found {← ppValue val}"

  partial def checkIndBlock (indBlockF : F) : TypecheckM Unit := do
    -- dbg_trace s!">> checkIndBlock"
    let quick := (← read).quick 
    let indBlock ← match derefConst indBlockF (← read).store with
      | .mutIndBlock blk => pure blk
      | _ => throw "Invalid Const kind. Expected mutIndBlock"

    -- Check all inductives
    let mut mutTypes := .empty
    for (indIdx, ind) in indBlock.enum do
      let f := mkInductiveProjF indBlockF indIdx quick
      -- dbg_trace s!">> checkIndBlock inductives: ind := {indIdx}, f := {f}"
      -- dbg_trace s!"{ppInductive ind}"
      let univs := List.range ind.lvls |>.map .var
      let (type, _) ← withEnv ⟨ [], univs ⟩ $ isSort ind.type
      let ctx ← read
      let stt ← get
      let typeSus := (suspend type {ctx with env := .mk ctx.env.exprs ·} stt)
      mutTypes := mutTypes.insert indIdx (f, typeSus)
      modify fun stt => { stt with typedConsts := stt.typedConsts.insert f (.inductive type ind.struct) }

    -- Check all constructors
    for (indIdx, ind) in indBlock.enum do
      let start := mutTypes.size
      for (cidx, ctor) in ind.ctors.enum do
        let f := mkConstructorProjF indBlockF indIdx cidx quick
        -- dbg_trace s!">> checkIndBlock constructors: ind := {indIdx}, cidx := {cidx}, f := {f}"
        -- dbg_trace s!"{ppExpr ctor.type}"
        let univs := List.range ctor.lvls |>.map .var
        let (type, _) ← withEnv ⟨ [], univs ⟩ $ withMutTypes mutTypes $ isSort ctor.type
        let ctx ← read
        let stt ← get
        let typeSus := (suspend type {ctx with env := .mk ctx.env.exprs ·} stt)
        mutTypes := mutTypes.insert (start + cidx) (f, typeSus)
        modify fun stt => { stt with typedConsts := stt.typedConsts.insert f (.constructor type ctor.idx ctor.fields) }

    -- Check all recursor types
    for (indIdx, ind) in indBlock.enum do
      let start := mutTypes.size
      for (ridx, recr) in ind.recrs.enum do
        let f := mkRecursorProjF indBlockF indIdx ridx quick
        -- dbg_trace s!">> checkIndBlock recursors: ind := {indIdx}, ridx := {ridx}, f := {f}"
        -- dbg_trace s!"{ppExpr recr.type}"
        let univs := List.range recr.lvls |>.map .var
        let (type, _) ← withEnv ⟨ [], univs ⟩ $ withMutTypes mutTypes $ isSort recr.type
        let ctx ← read
        let stt ← get
        let typeSus := (suspend type {ctx with env := .mk ctx.env.exprs ·} stt)
        mutTypes := mutTypes.insert (start + ridx) (f, typeSus)

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
        let recrConst := .recursor type recr.params recr.motives recr.minors recr.indices recr.isK indProj rules
        modify fun stt => { stt with typedConsts := stt.typedConsts.insert f recrConst }

    -- dbg_trace s!">> checkIndBlock end"
    return ()

  /-- Typechecks a `Yatima.Const`. The `TypecheckM Unit` computation finishes if the check finishes,
  otherwise a `TypecheckError` is thrown in some other function in the typechecker stack.

  Note that inductives, constructors, and recursors are constructed to typecheck, so this function
  only has to check the other `Const` constructors.
  -/
  partial def checkConst (f : F) : TypecheckM Unit := withResetCtx do
    -- dbg_trace s!">> checkConst {(← read).constNames.getF f}"
    match (← get).typedConsts.find? f with
    | some _ => 
      -- dbg_trace s!"cache hit"
      pure ()
    | none =>
      let c := derefConst f (← read).store
      if c.isMutType then return ()
      -- dbg_trace s!"{← ppConst c}"
      let univs := List.range (← c.levels) |>.map .var
      -- dbg_trace s!"checkConst with univs: {univs.map PP.ppUniv}"
      withEnv ⟨ [], univs ⟩ do
        let quick := (← read).quick
        let newConst ← match c with
          | .axiom ax =>
            -- dbg_trace s!"axiom"
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
            -- dbg_trace s!"opaque"
            let (type, _) ← isSort data.type
            let typeSus := suspend type (← read) (← get)
            -- dbg_trace s!"do a check 3"
            let value ← withRecF f $ check data.value typeSus
            pure $ TypedConst.opaque type value
          | .theorem data =>
            -- dbg_trace s!"theorem"
            let (type, _) ← isSort data.type
            let typeSus := suspend type (← read) (← get)
            -- dbg_trace s!"do a check 4"
            let value ← withRecF f $ check data.value typeSus
            pure $ TypedConst.theorem type value
          | .definition data =>
            -- dbg_trace s!"definition"
            let (type, _) ← isSort data.type
            let ctx ← read
            let typeSus := suspend type ctx (← get)
            -- dbg_trace s!"definition type:\n{typeSus.get}"
            let value ←
              if data.part then
                let mutTypes :=
                  let typeSus := (suspend type {ctx with env := .mk ctx.env.exprs ·} (← get))
                  (default : RecrCtx).insert 0 (f, typeSus)
                -- dbg_trace s!"do a check 5"
                withMutTypes mutTypes $ withRecF f $ check data.value typeSus
              else withRecF f $ check data.value typeSus
            pure $ TypedConst.definition type value data.part
          | .definitionProj p@⟨defBlockF, _⟩ =>
            -- dbg_trace s!"definition proj"
            let data ← getDefFromProj p
            -- dbg_trace s!"{ppDefinition data}"
            let (type, _) ← isSort data.type
            let ctx ← read
            let defBlock ← match derefConst defBlockF ctx.store with
              | .mutDefBlock blk => pure blk
              | _ => throw "Invalid Const kind. Expected mutDefBlock"
            let typeSus := suspend type ctx (← get)
            let value ←
              if data.part then
                -- check order should be the same as `recrCtx` in CA
                let mutTypes ← defBlock.enum.foldlM (init := default) fun acc (i, defn) => do
                  let defProjF := mkDefinitionProjF defBlockF i quick
                  -- TODO avoid repeated work here
                  let (type, _) ← isSort defn.type
                  let typeSus := (suspend type {ctx with env := .mk ctx.env.exprs ·} (← get))
                  pure $ acc.insert i (defProjF, typeSus)
                withMutTypes mutTypes $ withRecF f $ check data.value typeSus
              else withRecF f $ check data.value typeSus
            pure $ TypedConst.definition type value data.part
          | .inductiveProj ⟨indBlockF, _⟩ =>
            -- dbg_trace s!"inductive proj"
            checkIndBlock indBlockF
            return ()
          | .constructorProj ⟨indBlockF, _, _⟩ =>
            -- dbg_trace s!"constructor proj"
            checkIndBlock indBlockF
            return ()
          | .recursorProj ⟨indBlockF, _, _⟩ =>
            -- dbg_trace s!"recursor proj"
            checkIndBlock indBlockF
            return ()
          | .quotient data => 
            -- dbg_trace s!"quotient"
            let (type, _) ← isSort (← c.type)
            pure $ .quotient type data.kind
          | _ => throw "Impossible case. Cannot typecheck a mutual block."
        -- TODO is it okay to use the original hash for the `TypedConst`, or should we compute a new one?
        -- dbg_trace s!"finish {(← read).constNames.getF f}\n"
        modify fun stt => { stt with typedConsts := stt.typedConsts.insert f newConst }
end

end Yatima.Typechecker
