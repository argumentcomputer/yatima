import Yatima.Env

import Lean

namespace Yatima.Compiler.FromLean

instance : Coe Lean.Name Name where
  coe := .ofLeanName

instance : Coe Lean.BinderInfo BinderInfo where coe
  | .default        => .default
  | .auxDecl        => .auxDecl
  | .instImplicit   => .instImplicit
  | .strictImplicit => .strictImplicit
  | .implicit       => .implicit

instance : Coe Lean.Literal Literal where coe
  | .natVal n => .nat n
  | .strVal s => .str s

instance : Coe Lean.DefinitionSafety DefinitionSafety where coe
  | .safe      => .safe
  | .«unsafe»  => .«unsafe»
  | .«partial» => .«partial»

instance : Coe Lean.QuotKind QuotKind where coe
  | .type => .type
  | .ind  => .ind
  | .lift => .lift
  | .ctor => .ctor

abbrev EnvM := ReaderT Lean.ConstMap $ EStateM String Env

def EnvM.run (constMap : Lean.ConstMap) (state : Env) (m : EnvM α) :
    Except String Env :=
  match EStateM.run (ReaderT.run m constMap) state with
  | .ok _ env  => .ok env
  | .error e _ => .error e

def addUniv (univCid : UnivCid) (univ : Univ) : EnvM PUnit := do
  let env ← get
  set { env with univs := env.univs.insert univCid univ }

def addUnivAnon (univAnonCid : UnivAnonCid) (univAnon : UnivAnon) :
    EnvM PUnit := do
  let env ← get
  set { env with univ_anon := env.univ_anon.insert univAnonCid univAnon }

def addUnivMeta (univMetaCid : UnivMetaCid) (univMeta : UnivMeta) :
    EnvM PUnit := do
  let env ← get
  set { env with univ_meta := env.univ_meta.insert univMetaCid univMeta }

def addExpr (exprCid : ExprCid) (e : Expr) : EnvM PUnit := do
  let env ← get
  set { env with exprs := env.exprs.insert exprCid e }

def addExprAnon (exprAnonCid : ExprAnonCid) (exprAnon : ExprAnon) :
    EnvM PUnit := do
  let env ← get
  set { env with expr_anon := env.expr_anon.insert exprAnonCid exprAnon }

def addExprMeta (exprMetaCid : ExprMetaCid) (exprMeta : ExprMeta) :
    EnvM PUnit := do
  let env ← get
  set { env with expr_meta := env.expr_meta.insert exprMetaCid exprMeta }

def addConst (constCid : ConstCid) (const : Const) : EnvM PUnit := do
  let env ← get
  set { env with consts := env.consts.insert constCid const }

def addConstAnon (constAnonCid : ConstAnonCid) (constAnon : ConstAnon) :
    EnvM PUnit := do
  let env ← get
  set { env with const_anon := env.const_anon.insert constAnonCid constAnon }

def addConstMeta (constMetaCid : ConstMetaCid) (constMeta : ConstMeta) :
    EnvM PUnit := do
  let env ← get
  set { env with const_meta := env.const_meta.insert constMetaCid constMeta }

def univToCid (u : Univ) : EnvM UnivCid := do
  let univAnon : UnivAnon := sorry
  let univAnonCid : UnivAnonCid := sorry
  addUnivAnon univAnonCid univAnon
  let univMeta : UnivMeta := sorry
  let univMetaCid : UnivMetaCid := sorry
  addUnivMeta univMetaCid univMeta
  return ⟨univAnonCid, univMetaCid⟩

def exprToCid (e : Expr) : EnvM ExprCid := do
  let exprAnon : ExprAnon := sorry
  let exprAnonCid : ExprAnonCid := sorry
  addExprAnon exprAnonCid exprAnon
  let exprMeta : ExprMeta := sorry
  let exprMetaCid : ExprMetaCid := sorry
  addExprMeta exprMetaCid exprMeta
  return ⟨exprAnonCid, exprMetaCid⟩

def constToCid (c : Const) : EnvM ConstCid := do
  let constAnon : ConstAnon := sorry
  let constAnonCid : ConstAnonCid := sorry
  addConstAnon constAnonCid constAnon
  let constMeta : ConstMeta := sorry
  let constMetaCid : ConstMetaCid := sorry
  addConstMeta constMetaCid constMeta
  return ⟨constAnonCid, constMetaCid⟩

mutual

  partial def toYatimaUniv (lvls : List Lean.Name) : Lean.Level → EnvM Univ
  | .zero _      => return .zero
  | .succ n _    => do
    let univ ← toYatimaUniv lvls n
    let univCid ← univToCid univ
    addUniv univCid univ
    return .succ univCid
  | .max  a b _  => do
    let univA ← toYatimaUniv lvls a
    let univACid ← univToCid univA
    addUniv univACid univA
    let univB ← toYatimaUniv lvls b
    let univBCid ← univToCid univB
    addUniv univBCid univB
    return .max univACid univBCid
  | .imax a b _  => do
    let univA ← toYatimaUniv lvls a
    let univACid ← univToCid univA
    addUniv univACid univA
    let univB ← toYatimaUniv lvls b
    let univBCid ← univToCid univB
    addUniv univBCid univB
    return .imax univACid univBCid
  | .param nam _ => match lvls.indexOf nam with
    | some n => return .param nam n
    | none   => throw s!"'{nam}' not found in '{lvls}'"
  | .mvar .. => throw "Unfilled level metavariable"

  partial def toYatimaRecursorRule
    (ctorCid : ConstCid) (rules : Lean.RecursorRule) :
      EnvM RecursorRule := do
    let rhs ← toYatimaExpr [] rules.rhs
    let rhsCid ← exprToCid rhs
    addExpr rhsCid rhs
    return ⟨ctorCid, rules.nfields, rhsCid⟩

  partial def toYatimaExpr (levelParams : List Lean.Name) :
      Lean.Expr → EnvM Expr
    | .bvar idx _ => return .var "" idx
    | .sort lvl _ => do
      let univ ← toYatimaUniv levelParams lvl
      addUniv (← univToCid univ) univ
      return .sort (← toYatimaUniv levelParams lvl)
    | .const nam lvls _ => do
      match (← read).find?' nam with
      | some leanConst =>
        let const ← toYatimaConst leanConst
        let constId ← constToCid const
        addConst constId const
        let univs ← lvls.mapM $ toYatimaUniv levelParams
        for univ in univs do
          addUniv (← univToCid univ) univ
        return .const nam constId univs
      | none => throw s!"Unknown constant '{nam}'"
    | .app fnc arg _ => do
      let fnc ← toYatimaExpr levelParams fnc
      addExpr (← exprToCid fnc) fnc
      let arg ← toYatimaExpr levelParams arg
      addExpr (← exprToCid arg) arg
      return .app fnc arg
    | .lam nam bnd bod _ => do
      let bndInfo := bnd.binderInfo
      let bnd ← toYatimaExpr levelParams bnd
      addExpr (← exprToCid bnd) bnd
      let bod ← toYatimaExpr levelParams bod
      addExpr (← exprToCid bod) bod
      return .lam nam bndInfo bnd bod
    | .forallE nam dom img _ => do
      let bndInfo := dom.binderInfo
      let dom ← toYatimaExpr levelParams dom
      addExpr (← exprToCid dom) dom
      let img ← toYatimaExpr levelParams img
      addExpr (← exprToCid img) img
      return .pi nam bndInfo dom img
    | .letE nam typ exp bod _ => do
      let typ ← toYatimaExpr levelParams typ
      addExpr (← exprToCid typ) typ
      let exp ← toYatimaExpr levelParams exp
      addExpr (← exprToCid exp) exp
      let bod ← toYatimaExpr levelParams bod
      addExpr (← exprToCid bod) bod
      return .letE nam typ exp bod
    | .lit lit _ => return Yatima.Expr.lit lit
    | .mdata _ e _ => toYatimaExpr levelParams e
    | .proj .. => sorry
    | .fvar .. => sorry
    | .mvar .. => sorry

  partial def toYatimaConst : Lean.ConstantInfo → EnvM Const
    | .axiomInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addExpr typeCid type
      return .axiom {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        safe := not struct.isUnsafe }
    | .thmInfo struct => do
      let type  ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addExpr typeCid type
      let value ← toYatimaExpr struct.levelParams struct.value
      let valueCid ← exprToCid value
      addExpr valueCid value
      return .theorem {
        name  := struct.name
        lvls  := struct.levelParams.map .ofLeanName
        type  := typeCid
        value := valueCid }
    | .opaqueInfo struct => do
      let type  ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addExpr typeCid type
      let value ← toYatimaExpr struct.levelParams struct.value
      let valueCid ← exprToCid value
      addExpr valueCid value
      return .opaque {
        name  := struct.name
        lvls  := struct.levelParams.map .ofLeanName
        type  := typeCid
        value := valueCid
        safe  := not struct.isUnsafe }
    | .defnInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addExpr typeCid type
      let value ← toYatimaExpr struct.levelParams struct.value
      let valueCid ← exprToCid value
      addExpr valueCid value
      return .definition {
        name   := struct.name
        lvls   := struct.levelParams.map .ofLeanName
        type   := typeCid
        value  := valueCid
        safety := struct.safety }
    | .ctorInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addExpr typeCid type
      match (← read).find? struct.induct with
      | some leanConst =>
        let const ← toYatimaConst leanConst
        let constId ← constToCid const
        addConst constId const
        return .constructor {
          name := struct.name
          lvls := struct.levelParams.map .ofLeanName
          type := typeCid
          ind  := constId
          idx  := struct.cidx
          params := struct.numParams
          fields := struct.numFields
          safe := not struct.isUnsafe }
      | none => throw s!"Unknown constant '{struct.induct}'"
    | .inductInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addExpr typeCid type
      return .inductive {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        params := struct.numParams
        indices := struct.numIndices
        ctors := struct.ctors.map .ofLeanName
        recr := struct.isRec
        refl := struct.isReflexive
        nest := struct.isNested
        safe := not struct.isUnsafe }
    | .recInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addExpr typeCid type
      let inductName := struct.getInduct
      match (← read).find? inductName with
      | some leanConst =>
        let const ← toYatimaConst leanConst
        let constId ← constToCid const
        addConst constId const
        return .recursor {
          name := struct.name
          lvls := struct.levelParams.map .ofLeanName
          type := typeCid
          params := struct.numParams
          ind := constId
          motives := struct.numMotives
          indices := struct.numIndices
          minors := struct.numMinors
          rules := ← struct.rules.mapM $ toYatimaRecursorRule constId
          k := struct.k
          safe := not struct.isUnsafe }
      | none => throw s!"Unknown constant '{inductName}'"
    | .quotInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addExpr typeCid type
      return .quotient {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        kind := struct.kind }

end

def buildEnv (constMap : Lean.ConstMap) : EnvM Env := do
  constMap.forM fun _ leanConst => do
    let yatimaConst ← toYatimaConst leanConst
    let constCid ← constToCid yatimaConst
    addConst constCid yatimaConst
  get

def extractEnv (constMap : Lean.ConstMap) : Except String Env :=
  EnvM.run constMap default (buildEnv constMap)

end Yatima.Compiler.FromLean
