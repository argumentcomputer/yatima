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

def piInfo : TypeInfo → TypeInfo
| .prop => .prop
| _ => .none

def reduceDecUniv (u : DecUniv) : TypecheckM DecUniv := do
  let u : DecUniv ← match u with
  | .init lvl => pure $ DecUniv.init $ Univ.instBulkReduce (← read).env.univs lvl
  | .dec dlvl => pure $ DecUniv.dec $ ← reduceDecUniv dlvl
  match u with
  | .dec (.init (Univ.succ lvl)) => pure $ .init lvl
  | u => pure u

/--
  Gives the correct type information for a term based on its type.
-/
def infoFromType (typ : SusValue) : TypecheckM TypeInfo :=
  match typ.info with
  | .prop => pure .proof
  | .sort lvl => do
    let lvl := Univ.instBulkReduce (← read).env.univs lvl
    match lvl with 
    | .succ lvl => pure $ .sort lvl
    | .zero => pure .prop
    | _ => pure $ .decSort $ .init lvl
  | .decSort dlvl => do match (← reduceDecUniv dlvl) with
    | .init (Univ.succ lvl) => pure $ .sort lvl
    | _ => pure $ .decSort $ .dec dlvl
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
  Checks if `term : Expr` has type `type : SusValue`. Returns the typed IR for `term`
  -/
  partial def check (term : Expr) (type : SusValue) : TypecheckM TypedExpr := do
    --dbg_trace s!"checking: {term} : {type.get}"
    let (term, inferType) ← infer term
    -- discard any suspended TypeInfo
    let inferInfo := match inferType.info with
    | .sort _
    | .decSort _ => TypeInfo.none
    | _ => inferType.info
    let typeInfo := match type.info with
    | .sort _
    | .decSort _ => TypeInfo.none
    | _ => type.info
    if !(inferInfo == typeInfo) || !(← equal (← read).lvl type inferType) then
      --dbg_trace s!"mismatch (inferred, expected): {repr inferType.info} → {repr inferInfo}, {repr type.info} → {repr typeInfo}"
      --dbg_trace s!"failed checking: {term} : {type.get}"
      throw $ .valueMismatch (toString type.get) (toString inferType.get)
    else
      --dbg_trace s!"done checking: {term} : {type.get}"
      pure term

  /-- Infers the type of `term : Expr`. Returns the typed IR for `term` along with its inferred type  -/
  partial def infer (term : Expr) : TypecheckM (TypedExpr × SusValue) := do
    match term with
    | .var name idx =>
      let types := (← read).types
      let some type := types.get? idx | throw $ .outOfEnvironmentRange name idx types.length
      let term := .var (← infoFromType type) name idx
      pure (term, type)
    | .sort lvl =>
      let univs := (← read).env.univs
      let lvl := Univ.succ (Univ.instBulkReduce univs lvl)
      let typ := .mk .none ⟨ fun _ => .sort lvl ⟩
      return (.sort (.sort lvl) lvl, typ)
    | .app fnc arg =>
      let (fnc, fncType) ← infer fnc
      match fncType.get with
      | .pi _ _ dom img env =>
        --dbg_trace s!"applying: {fnc} to {arg} : {dom.get} with {repr dom.info}"
        let arg ← check arg dom
        --dbg_trace s!"done applying: {fnc} to {arg}"
        let typ := suspend img { ← read with env := env.extendWith $ suspend arg (← read) (← get)} (← get)
        let term := .app (← infoFromType typ) fnc arg
        --dbg_trace s!"info for {typ.get}: {repr img.info}, {repr term.info}"
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
        Value.pi name bind domVal (← quote (ctx.lvl+1) img.info img.get) ctx.env
      pure (term, typ)
    | .pi name bind dom img =>
      --dbg_trace s!"pi getting dom: {name}"
      let (dom, domLvl) ← isSort dom
      --dbg_trace s!"pi done getting dom: {name}"
      --dbg_trace s!"domain info: {dom}: {repr dom.info}"
      let ctx ← read
      let domVal := suspend dom ctx (← get)
      withExtendedCtx (mkSusVar (← infoFromType domVal) name ctx.lvl) domVal $ do
        --dbg_trace s!"getting sort of: {img}"
        let (img, imgLvl) ← isSort img
        --dbg_trace s!"done getting sort {imgLvl} of: {img}"
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
      let some (ind, ctor, univs, params) ← isStruct exprType.get
        | throw $ .typNotStructure (toString exprType.get)
      -- annotate constructor type
      let (ctorType, _) ← infer ctor.type
      let mut ctorType ← applyType (← withEnv ⟨[], univs⟩ $ eval ctorType) params.reverse
      for i in [:idx] do
        match ctorType with
        | .pi _ _ dom img piEnv =>
          let info ← infoFromType dom
          let proj := suspend (.proj info ind i expr) (← read) (← get)
          ctorType ← withNewExtendedEnv piEnv proj $ eval img
        | _ => pure ()
      match ctorType with
      | .pi _ _ dom _ _  =>
        match exprType.info, dom.info with
        | .prop, .prop =>
          let term := .proj (← infoFromType dom) ind idx expr
          pure (term, dom)
        | .prop, _ =>
          throw $ .projEscapesProp s!"{toString expr}.{idx}"
        | _, _ =>
          let term := .proj (← infoFromType dom) ind idx expr
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
        | .theorem    data
        | .opaque     data
        | .definition data => do
          let (type, _) ← isSort data.type
          let typeSus := suspend type (← read) (← get)
          let value ← match c with
          | .definition data => match data.safety with
            | .partial =>
              let mutTypes : Std.RBMap ConstIdx SusValue compare ← data.all.foldlM (init := default) fun acc k => do
                let const ← derefConst default k
                -- TODO avoid repeated work here
                let (type, _) ← isSort data.type
                let typeSus := suspend type (← read) (← get)
                match const with
                | .theorem    data
                | .opaque     data
                | .definition data => pure $ acc.insert k typeSus
                | _ => throw .impossible -- FIXME better error
              withMutTypes mutTypes $ check data.value typeSus
            | _ => check data.value typeSus
          | _ => check data.value typeSus

          -- update the typechecked consts with the annotated values/types
          let tcConsts := (← get).tcConsts
          if h : idx < tcConsts.size then
            let newConst ← match c with
            | .theorem    data => pure $ TypedConst.theorem type value
            | .opaque     data => pure $ TypedConst.opaque type value
            | .definition data => pure $ TypedConst.definition type value data.safety
            | _ => throw .impossible
            modify fun stt => {stt with tcConsts := tcConsts.set ⟨idx, h⟩ $ .some newConst}
          else
            throw $ .impossible
        -- TODO: check that inductives, condataors and recursors are well-formed
        -- TODO: check that quotient is well-formed. I guess it is possible to do this
        -- while converting from Ipld by checking the cids of the quotient constants
        -- with precomputed ones
        | .axiom       data
        | .inductive   data
        | .constructor data
        | .extRecursor data
        | .intRecursor data
        | .quotient    data =>
          --dbg_trace s!"checking constant type: {data.name}"
          let (type, _)  ← isSort data.type
          --dbg_trace s!"done checking constant type: {data.name}"

          -- update the typechecked consts with the annotated values/types
          let tcConsts := (← get).tcConsts
          if h : idx < tcConsts.size then
            let newConst ← match c with
            | .axiom       _ => pure $ TypedConst.axiom type
            | .inductive   data => pure $ TypedConst.inductive type data.struct.isSome
            | .constructor data =>
              let typeSus := suspend type (← read) (← get)
                -- rhs` can have recursive references to `c`, so we must `withMutTypes`
              let mutTypes : Std.RBMap ConstIdx SusValue compare := default
              let (rhs, _) ← withMutTypes (mutTypes.insert idx typeSus) $ infer data.rhs
              pure $ TypedConst.constructor type rhs data.idx data.fields
            | .extRecursor data =>
              let rules ← data.rules.mapM fun rule => do
                -- rhs` can have recursive references to `c`, so we must `withMutTypes`
                let typeSus := suspend type (← read) (← get)
                let mutTypes : Std.RBMap ConstIdx SusValue compare := default
                let (rhs, _) ← withMutTypes (mutTypes.insert idx typeSus) $ infer rule.rhs
                pure (rule.ctor.idx, rule.fields, rhs)
              pure $ .extRecursor type data.params data.motives data.minors data.indices rules
            | .intRecursor data => pure $ .intRecursor type data.params data.motives data.minors data.indices data.k
            | .quotient    data => pure $ .quotient type data.kind
            | _ => throw $ .impossible
            modify fun stt => {stt with tcConsts := tcConsts.set ⟨idx, h⟩ $ .some newConst}
          else
            throw $ .impossible
    | .none =>
      throw .impossible
    | _ => pure ()
end

end Yatima.Typechecker
