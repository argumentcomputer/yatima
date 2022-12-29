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

def isStruct : Value → TypecheckM (Option (ConstIdx × Constructor × List Univ × List SusValue))
  | .app (.const name k univs) params => do
    match ← derefConst name k with
    | .inductive ind => do
      match ind.struct with
        | some ctorIdx => do
          let ctor ← match (← read).store.consts.get? ctorIdx with
            | some (.constructor ctor) => pure ctor
            | _ => throw .impossible
          -- Sanity check
          if ind.params != params.length then throw .impossible else
          pure (k, ctor, univs, (params.map (·.1)))
        | none => pure none
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
def infoFromType (typ : SusValue) : TypecheckM TypeInfo := do
  match typ.info with
  | .prop => pure .proof
  | _ => do
    match typ.get with
    | .app (.const name i _) _ => do
      match ← derefConst name i with
      | .inductive induct => if induct.unit then pure .unit else pure .none
      | _ => pure .none
    | .sort lvl => if lvl.isZero then pure .prop else pure .none
    | _ => pure .none

def susInfoFromType (typ : SusValue) : TypecheckM SusTypeInfo := do
  match typ.info with
  | .prop => pure .proof
  | _ => do
    match typ.get with
    | .app (.const name i _) _ => do
      match ← derefConst name i with
      | .inductive induct => if induct.unit then pure .unit else pure .none
      | _ => pure .none
    | .sort lvl => if lvl.isZero then pure .prop else pure (.sort lvl)
    | _ => pure .none

mutual
  /--
  Checks if `term : Expr` has type `type : SusValue`. Returns the typed IR for `term`
  -/
  partial def check (term : Expr) (type : SusValue) : TypecheckM TypedExpr := do
    let (term, inferType) ← infer term
    if !(inferType.info == type.info) || !(← equal (← read).lvl type inferType) then
      throw $ .valueMismatch (toString type.get) (toString inferType.get)
    else
      pure term

  /-- Infers the type of `term : Expr`. Returns the typed IR for `term` along with its inferred type  -/
  partial def infer (term : Expr) : TypecheckM (TypedExpr × SusValue) := do
    match term with
    | .var name idx =>
      let types := (← read).types
      let some type := types.get? idx | throw $ .outOfEnvironmentRange name idx types.length
      let term := .var (← susInfoFromType type) name idx
      pure (term, type)
    | .sort lvl =>
      let univs := (← read).env.univs
      let lvl := Univ.instBulkReduce univs lvl
      let lvl' := Univ.succ lvl
      let typ := .mk .none ⟨ fun _ => .sort lvl' ⟩
      -- NOTE: we populate `SusTypeInfo.sort` here for consistency but technically it isn't necessary
      -- because `lvl'` can never become `Univ.zero`.
      return (.sort (.sort lvl') lvl, typ)
    | .app fnc arg =>
      let (fnc, fncType) ← infer fnc
      match fncType.get with
      | .pi _ _ dom img env =>
        let arg ← check arg dom
        let typ := suspend img { ← read with env := env.extendWith $ suspend arg (← read) (← get)} (← get)
        let term := .app (← susInfoFromType typ) fnc arg
        pure (term, typ)
      | val => throw $ .notPi (toString val)
    | .lam name bind dom bod  =>
      let (dom, _) ← isSort dom
      let ctx ← read
      let domVal := suspend dom ctx (← get)
      let var := mkSusVar (← infoFromType domVal) name ctx.lvl
      let (bod, img) ← withExtendedCtx var domVal $ infer bod
      let term := .lam (lamInfo bod.info) name bind dom bod
      let typ := .mk (piInfo img.info) $
        Value.pi name bind domVal (← quote (ctx.lvl+1) img.info.toSus ctx.env img.get) ctx.env
      pure (term, typ)
    | .pi name bind dom img =>
      let (dom, domLvl) ← isSort dom
      let ctx ← read
      let domVal := suspend dom ctx (← get)
      withExtendedCtx (mkSusVar (← infoFromType domVal) name ctx.lvl) domVal $ do
        let (img, imgLvl) ← isSort img
        let typ := .mk .none ⟨ fun _ => .sort $ .reduceIMax domLvl imgLvl ⟩
        let term := .pi (← susInfoFromType typ) name bind dom img
        return (term, typ)
    | .letE name expType exp bod =>
      let (expType, _) ← isSort expType
      let expTypeVal := suspend expType (← read) (← get)
      let exp ← check exp expTypeVal
      let expVal := suspend exp (← read) (← get)
      let (bod, typ) ← withExtendedCtx expVal expTypeVal $ infer bod
      let term := .letE bod.info name expType exp bod
      return (term, typ)
    | .lit (.natVal v) =>
      let typ := .mk .none (mkConst `Nat (← primIndex .nat) [])
      pure $ (.lit .none (.natVal v), typ)
    | .lit (.strVal s) =>
      let typ := .mk .none (mkConst `String (← primIndex .string) [])
      pure $ (.lit .none (.strVal s), typ)
    | .const name k constUnivs =>
      if let some typ := (← read).mutTypes.find? k then
        let typ := typ (constUnivs.map (Univ.instBulkReduce (← read).env.univs))
        -- mutual references are assumed to typecheck
        pure (.const (← susInfoFromType typ) name k constUnivs, typ)
      else
        let univs := (← read).env.univs
        let const ← derefConst name k
        checkConst const k
        let tconst ← derefTypedConst name k
        let env := ⟨[], constUnivs.map (Univ.instBulkReduce univs)⟩
        let typ := suspend tconst.type { ← read with env := env } (← get)
        pure (.const (← susInfoFromType typ) name k constUnivs, typ)
    | .proj idx expr =>
      let (expr, exprType) ← infer expr
      let some (ind, ctor, univs, params) ← isStruct exprType.get
        | throw $ .typNotStructure (toString exprType.get)
      -- annotate constructor type
      let (ctorType, _) ← infer ctor.type
      let mut ctorType ← applyType (← withEnv ⟨[], univs⟩ $ eval ctorType) params.reverse
      for i in [:idx] do
        match ctorType with
        | .pi _ _ dom img piEnv =>
          let info ← susInfoFromType dom
          let proj := suspend (.proj info ind i expr) (← read) (← get)
          ctorType ← withNewExtendedEnv piEnv proj $ eval img
        | _ => pure ()
      match ctorType with
      | .pi _ _ dom _ _  =>
        match exprType.info, dom.info with
        | .prop, .prop =>
          let term := .proj (← susInfoFromType dom) ind idx expr
          pure (term, dom)
        | .prop, _ =>
          throw $ .projEscapesProp s!"{toString expr}.{idx}"
        | _, _ =>
          let term := .proj (← susInfoFromType dom) ind idx expr
          pure (term, dom)
      | _ => throw .impossible

  /--
  Checks if `expr : Expr` is `Sort lvl` for some level `lvl`, and throws `TypecheckerError.notTyp`
  if it is not.
  -/
  partial def isSort (expr : Expr) : TypecheckM (TypedExpr × Univ) := do
    let (expr, typ) ← infer expr
    match typ.get with
    | .sort u => pure (expr, u)
    | val => throw $ .notTyp (toString val)

  /-- Typechecks a `Yatima.Const`. The `TypecheckM Unit` computation finishes if the check finishes,
  otherwise a `TypecheckError` is thrown in some other function in the typechecker stack.

  Note that inductives, constructors, and recursors are constructed to typecheck, so this function
  only has to check the other `Const` constructors.
  -/
  partial def checkConst (c : Const) (idx : Nat) : TypecheckM Unit := withResetCtx c.name do
    match (← get).tcConsts.get? idx with
    | .some .none =>
      let univs := c.levels.foldr
        (fun name cont i => Univ.var name i :: (cont (i + 1)))
        (fun _ => []) 0
      withEnv ⟨ [], univs ⟩ $ do
        let (type, _) ← isSort c.type
        let newConst ← match c with
        | .axiom       _    => pure $ TypedConst.axiom type
        | .opaque  data =>
          let typeSus := suspend type (← read) (← get)
          let value ← check data.value typeSus
          pure $ TypedConst.opaque type value
        | .theorem data =>
          let typeSus := suspend type (← read) (← get)
          let value ← check data.value typeSus
          pure $ TypedConst.theorem type value
        | .definition  data =>
          let typeSus := suspend type (← read) (← get)
          let value ← match data.safety with
            | .partial =>
              let mutTypes : Std.RBMap ConstIdx (List Univ → SusValue) compare ← data.all.foldlM (init := default) fun acc k => do
                let const ← derefConst default k
                -- TODO avoid repeated work here
                let (type, _) ← isSort const.type
                let ctx ← read
                let stt ← get
                let typeSus := fun univs => suspend type {ctx with env := .mk ctx.env.exprs univs} stt
                match const with
                | .definition _ => pure $ acc.insert k typeSus
                | _ => throw .impossible -- FIXME better error
              withMutTypes mutTypes $ check data.value typeSus
            | _ => check data.value typeSus
          pure $ TypedConst.definition type value data.safety
        | .inductive   data => pure $ .inductive type data.struct.isSome
        | .constructor data => pure $ .constructor type data.idx data.fields
        | .recursor data => do
          let mutTypes : Std.RBMap ConstIdx (List Univ → SusValue) compare ← data.all.foldlM (init := default) fun acc idx => do
            match (← read).store.consts.get? idx with
            | .some (.recursor data) =>
              -- FIXME repeated computation (this will happen again when we actually check the constructor on its own)
              let (type, _)  ← withMutTypes acc $ isSort data.type
              let ctx ← read
              let stt ← get
              let typeSus := fun univs => suspend type {ctx with env := .mk ctx.env.exprs univs} stt
              pure $ acc.insert idx typeSus
            | _ => pure acc
          let rules ← data.rules.mapM fun rule => do
            let (rhs, _) ← withMutTypes mutTypes $ infer rule.rhs
            pure (sorry, rule.fields, rhs)
          pure $ TypedConst.recursor type data.params data.motives data.minors data.indices data.isK data.ind rules
        | .quotient data => pure $ .quotient type data.kind
        let tcConsts := (← get).tcConsts
        if h : idx < tcConsts.size then
          modify fun stt => {stt with tcConsts := tcConsts.set ⟨idx, h⟩ $ .some newConst}
        else
          throw $ .impossible
    | .none => throw .impossible
    | _ => pure ()
end

end Yatima.Typechecker
