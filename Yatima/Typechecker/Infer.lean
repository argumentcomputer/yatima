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
        | some ctor =>
          -- Sanity check
          if ind.params != params.length then throw .impossible else
          pure (k, ctor, univs, params)
        | none => pure none
    | _ => pure none
  | _ => pure none

/--
  Gives the correct type information for a lambda based on the information of the body.
  No lambdas can be a proposition, a struct or be elements of the unit type.
-/
def lamInfo : TypeInfo → TypeInfo
| .proof => .proof
| _ => .none

/--
  Gives the correct type information for a term based on its type.
-/
def infoFromType (typ : SusValue) : TypecheckM TypeInfo :=
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

mutual
  /--
  Checks if `term : Expr` has type `type : SusValue`. Returns the expression with flags updated
  -/
  partial def check (term : Expr) (type : SusValue) : TypecheckM TypedExpr := do
    let (term, inferType) ← infer term
    if !(inferType.info == type.info) || !(← equal (← read).lvl type inferType) then
      throw $ .valueMismatch (toString type.get) (toString inferType.get)
    else
      pure term

  /-- Infers the type of `term : Expr`. Returns the expression with flags updated along with the inferred type  -/
  partial def infer (term : Expr) : TypecheckM (TypedExpr × SusValue) := do
    match term with
    | .var name idx =>
      let types := (← read).types
      let some type := types.get? idx | throw $ .outOfEnvironmentRange name idx types.length
      let term := .var (← infoFromType type) name idx
      pure (term, type)
    | .sort lvl =>
      let univs := (← read).env.univs
      let typ := .mk .none ⟨ fun _ => .sort $ .instBulkReduce univs lvl.succ ⟩
      return (.sort .none lvl, typ)
    | .app (.lam lamName bind lamDom bod) arg =>
      let (lamDom, _) ← isSort lamDom
      let lamDomVal := suspend lamDom (← read) (← get)
      let arg ← check arg lamDomVal
      let argVal := suspend arg (← read) (← get)
      let (bod, type) ← withExtendedCtx argVal lamDomVal $ infer bod
      pure (.app bod.info (.lam (lamInfo bod.info) lamName bind lamDom bod) arg, type)
    | .app fnc arg =>
      let (fnc, fncType) ← infer fnc
      match fncType.get with
      | .pi _ _ dom img env =>
        let arg ← check arg dom
        let typ := suspend img { ← read with env := env.extendWith $ suspend arg (← read) (← get)} (← get)
        let term := .app (← infoFromType typ) fnc arg
        pure (term, typ)
      | val => throw $ .notPi (toString val)
    | .lam .. => sorry
    | .pi name bind dom img =>
      let (dom, domLvl) ← isSort dom
      let ctx ← read
      let domVal := suspend dom ctx (← get)
      withExtendedCtx (mkSusVar (← infoFromType domVal) name ctx.lvl) domVal $ do
        let (img, imgLvl) ← isSort img
        let typ := .mk .none ⟨ fun _ => .sort $ .reduceIMax domLvl imgLvl ⟩
        let term := .pi (← infoFromType typ) name bind dom img
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
        -- mutual references are assumed to typecheck
        pure (.const (← infoFromType typ) name k constUnivs, typ)
      else
        let univs := (← read).env.univs
        let const ← derefConst name k
        withResetCtx $ checkConst const k
        let tconst ← derefTypedConst name k
        let env := ⟨[], constUnivs.map (Univ.instBulkReduce univs)⟩
        let typ := suspend tconst.type { ← read with env := env } (← get)
        pure (.const (← infoFromType typ) name k constUnivs, typ)
    | .proj idx expr =>
      let (expr, exprType) ← infer expr
      let some (struct, ctor, univs, params) ← isStruct exprType.get
        | throw $ .typNotStructure (toString exprType.get)
      -- annotate constructor type
      let (ctorType, _) ← infer ctor.type
      let mut ctorType ← applyType (← withEnv ⟨[], univs⟩ $ eval ctorType) params.reverse
      for i in [:idx] do
        match ctorType with
        | .pi _ _ dom img piEnv =>
          let info ← infoFromType dom
          let proj := suspend (.proj info struct i expr) (← read) (← get)
          ctorType ← withNewExtendedEnv piEnv proj $ eval img
        | _ => pure ()
      match ctorType with
      | .pi _ _ dom _ _  =>
        match exprType.info, dom.info with
        | .prop, .prop => 
          let term := .proj (← infoFromType dom) struct idx expr
          pure (term, dom)
        | .prop, _ => 
          throw $ .projEscapesProp s!"{toString expr}.{idx}"
        | _, _ => 
          let term := .proj (← infoFromType dom) struct idx expr
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
  partial def checkConst (c : Const) (idx : Nat) : TypecheckM Unit := do
    match (← get).tcConsts.get? idx with
    | .some .none =>
      let univs := c.levels.foldr
        (fun name cont i => Univ.var name i :: (cont (i + 1)))
        (fun _ => []) 0
      withEnv ⟨ [], univs ⟩ $ do
        match c with
        | .theorem    struct
        | .opaque     struct
        | .definition struct => do
          let (type, _) ← isSort struct.type
          let typeSus := suspend type (← read) (← get)
          let value ← match c with
          | .definition struct => match struct.safety with
            | .partial =>
              let mutTypes : Std.RBMap ConstIdx SusValue compare ← struct.all.foldlM (init := default) fun acc k => do
                let const ← derefConst default k
                -- TODO avoid repeated work here
                let (type, _) ← isSort struct.type
                let typeSus := suspend type (← read) (← get)
                match const with
                | .theorem    struct
                | .opaque     struct
                | .definition struct => pure $ acc.insert k typeSus
                | _ => throw .impossible -- FIXME better error
              withMutTypes mutTypes $ check struct.value typeSus
            | _ => check struct.value typeSus
          | _ => check struct.value typeSus

          -- update the typechecked consts with the annotated values/types
          let tcConsts := (← get).tcConsts
          if h : idx < tcConsts.size then
            let newConst ← match c with
            | .theorem    struct => pure $ Const'.theorem {struct with value, type}
            | .opaque     struct => pure $ .opaque {struct with value, type}
            | .definition struct => pure $ .definition {struct with value, type}
            | _ => throw .impossible
            modify fun stt => {stt with tcConsts := tcConsts.set ⟨idx, h⟩ $ .some newConst}
          else
            throw $ .impossible
        -- TODO: check that inductives, constructors and recursors are well-formed
        -- TODO: check that quotient is well-formed. I guess it is possible to do this
        -- while converting from Ipld by checking the cids of the quotient constants
        -- with precomputed ones
        | .axiom       struct
        | .inductive   struct
        | .constructor struct
        | .extRecursor struct
        | .intRecursor struct
        | .quotient    struct =>
          let (type, _)  ← isSort struct.type

          -- update the typechecked consts with the annotated values/types
          let tcConsts := (← get).tcConsts
          if h : idx < tcConsts.size then
            let newConst ← match c with 
            | .axiom       struct => pure $ Const'.axiom {struct with type}
            | .inductive   struct => pure $ .inductive {struct with type}
            | .constructor struct =>
              let (rhs, _) ← infer struct.rhs
              pure $ .constructor {struct with rhs, type}
            | .extRecursor struct => pure $ .extRecursor {struct with type}
            | .intRecursor struct => pure $ .intRecursor {struct with type}
            | .quotient    struct => pure $ .quotient {struct with type}
            | _ => throw $ .impossible
            modify fun stt => {stt with tcConsts := tcConsts.set ⟨idx, h⟩ $ .some newConst}
          else
            throw $ .impossible
    | .none =>
      throw .impossible
    | _ => pure ()
end

end Yatima.Typechecker
