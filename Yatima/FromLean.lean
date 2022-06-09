import Yatima.Env
import Yatima.ToIpld

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
  | .safe    => .safe
  | .unsafe  => .unsafe
  | .partial => .partial

instance : Coe Lean.QuotKind QuotKind where coe
  | .type => .type
  | .ind  => .ind
  | .lift => .lift
  | .ctor => .ctor

structure ToYatimaState where
  env        : Env
  nBinders   : Nat
  constSubst : Option Name
  deriving Inhabited

abbrev ToYatimaM := ReaderT Lean.ConstMap $ EStateM String ToYatimaState

def ToYatimaM.run (constMap : Lean.ConstMap)
  (state : ToYatimaState) (m : ToYatimaM α) :
    Except String Env :=
  match EStateM.run (ReaderT.run m constMap) state with
  | .ok _ stt  => .ok stt.env
  | .error e _ => .error e

inductive YatimaTuple
  | univ_cache  : UnivCid      → Univ      → YatimaTuple
  | univ_anon   : UnivAnonCid  → UnivAnon  → YatimaTuple
  | univ_meta   : UnivMetaCid  → UnivMeta  → YatimaTuple
  | expr_cache  : ExprCid      → Expr      → YatimaTuple
  | expr_anon   : ExprAnonCid  → ExprAnon  → YatimaTuple
  | expr_meta   : ExprMetaCid  → ExprMeta  → YatimaTuple
  | const_cache : ConstCid     → Const     → YatimaTuple
  | const_anon  : ConstAnonCid → ConstAnon → YatimaTuple
  | const_meta  : ConstMetaCid → ConstMeta → YatimaTuple

def addToEnv (y : YatimaTuple) : ToYatimaM PUnit := do
  let stt ← get
  let env := stt.env
  match y with
  | .univ_cache  cid obj => set { stt with env := { env with univ_cache  := env.univ_cache.insert cid obj } }
  | .univ_anon   cid obj => set { stt with env := { env with univ_anon   := env.univ_anon.insert cid obj } }
  | .univ_meta   cid obj => set { stt with env := { env with univ_meta   := env.univ_meta.insert cid obj } }
  | .expr_cache  cid obj => set { stt with env := { env with expr_cache  := env.expr_cache.insert cid obj } }
  | .expr_anon   cid obj => set { stt with env := { env with expr_anon   := env.expr_anon.insert cid obj } }
  | .expr_meta   cid obj => set { stt with env := { env with expr_meta   := env.expr_meta.insert cid obj } }
  | .const_cache cid obj => set { stt with env := { env with const_cache := env.const_cache.insert cid obj } }
  | .const_anon  cid obj => set { stt with env := { env with const_anon  := env.const_anon.insert cid obj } }
  | .const_meta  cid obj => set { stt with env := { env with const_meta  := env.const_meta.insert cid obj } }

def incrNBinders : ToYatimaM PUnit := do
  let stt ← get
  set { stt with nBinders := stt.nBinders.succ }

open ToIpld

def univToCid (u : Univ) : ToYatimaM UnivCid := do
  let univAnon : UnivAnon := u.toAnon
  let univAnonCid : UnivAnonCid := univAnonToCid univAnon
  addToEnv $ .univ_anon univAnonCid univAnon
  let univMeta : UnivMeta := u.toMeta
  let univMetaCid : UnivMetaCid := univMetaToCid univMeta
  addToEnv $ .univ_meta univMetaCid univMeta
  return ⟨univAnonCid, univMetaCid⟩

mutual

  def separateExpr (e : Expr) : ToYatimaM (ExprAnon × ExprMeta) :=
    match e with
    | .var nam n => return (.var n, .var nam)
    | .sort u    => return (.sort u.anon, .sort u.meta)
    | .const nam c ls =>
      return (.const c.anon $ ls.map (·.anon), .const nam c.meta $ ls.map (·.meta))
    | .app fnc arg => do
      let fncCid ← exprToCid fnc
      let argCid ← exprToCid arg
      return (.app fncCid.anon argCid.anon, .app fncCid.meta argCid.meta)
    | .lam nam bnd typ bod => do
      let typCid ← exprToCid typ
      let bodCid ← exprToCid bod
      return (.lam typCid.anon bodCid.anon, .lam nam bnd typCid.meta bodCid.meta)
    | .pi nam bnd dom img => do 
      let domCid ← exprToCid dom
      let imgCid ← exprToCid img
      return (.pi domCid.anon imgCid.anon, .pi nam bnd domCid.meta imgCid.meta)
    | .letE nam typ exp bod => do
      let typCid ← exprToCid typ
      let expCid ← exprToCid exp
      let bodCid ← exprToCid bod
      return (
        .letE typCid.anon expCid.anon bodCid.anon, 
        .letE typCid.meta expCid.meta bodCid.meta
      )
    | .lit lit => return (.lit lit, .lit)
    | .lty lty => return (.lty lty, .lty)
    | .fix nam exp => do
      let expCid ← exprToCid exp
      return (.fix expCid.anon, .fix nam expCid.meta)
    | .proj idx exp => do
      let expCid ← exprToCid exp
      return (.proj idx expCid.anon, .proj idx expCid.meta)

  def exprToCid (e : Expr) : ToYatimaM ExprCid := do
    let (exprAnon, exprMeta) ← separateExpr e
    let exprAnonCid : ExprAnonCid := exprAnonToCid exprAnon
    addToEnv $ .expr_anon exprAnonCid exprAnon
    let exprMetaCid : ExprMetaCid := exprMetaToCid exprMeta
    addToEnv $ .expr_meta exprMetaCid exprMeta
    return ⟨exprAnonCid, exprMetaCid⟩

end

def constToCid (c : Const) : ToYatimaM ConstCid := do
  let constAnon : ConstAnon := c.toAnon
  let constAnonCid : ConstAnonCid := constAnonToCid constAnon
  addToEnv $ .const_anon constAnonCid constAnon
  let constMeta : ConstMeta := c.toMeta
  let constMetaCid : ConstMetaCid := constMetaToCid constMeta
  addToEnv $ .const_meta constMetaCid constMeta
  return ⟨constAnonCid, constMetaCid⟩

def toYatimaUniv (lvls : List Lean.Name) : Lean.Level → ToYatimaM Univ
  | .zero _      => return .zero
  | .succ n _    => do
    let univ ← toYatimaUniv lvls n
    let univCid ← univToCid univ
    addToEnv $ .univ_cache univCid univ
    return .succ univCid
  | .max  a b _  => do
    let univA ← toYatimaUniv lvls a
    let univACid ← univToCid univA
    addToEnv $ .univ_cache univACid univA
    let univB ← toYatimaUniv lvls b
    let univBCid ← univToCid univB
    addToEnv $ .univ_cache univBCid univB
    return .max univACid univBCid
  | .imax a b _  => do
    let univA ← toYatimaUniv lvls a
    let univACid ← univToCid univA
    addToEnv $ .univ_cache univACid univA
    let univB ← toYatimaUniv lvls b
    let univBCid ← univToCid univB
    addToEnv $ .univ_cache univBCid univB
    return .imax univACid univBCid
  | .param nam _ => match lvls.indexOf nam with
    | some n => return .param nam n
    | none   => throw s!"'{nam}' not found in '{lvls}'"
  | .mvar .. => throw "Unfilled level metavariable"

mutual

  partial def toYatimaRecursorRule
    (levelParams : List Lean.Name) (ctorCid : ConstCid) (rules : Lean.RecursorRule) :
      ToYatimaM RecursorRule := do
    let rhs ← toYatimaExpr levelParams rules.rhs
    let rhsCid ← exprToCid rhs
    addToEnv $ .expr_cache rhsCid rhs
    return ⟨ctorCid, rules.nfields, rhsCid⟩

  partial def toYatimaExpr (levelParams : List Lean.Name) :
      Lean.Expr → ToYatimaM Expr
    | .bvar idx _ => return .var "" idx
    | .sort lvl _ => do
      let univ ← toYatimaUniv levelParams lvl
      let univCid ← univToCid univ
      addToEnv $ .univ_cache univCid univ
      return .sort univCid
    | .const nam lvls _ => do match (← get).constSubst with
      | some varName =>
        set { (← get) with constSubst := none }
        return .var varName (← get).nBinders
      | none         => match (← read).find?' nam with
        | some leanConst =>
          let const ← toYatimaConst leanConst
          let constId ← constToCid const
          addToEnv $ .const_cache constId const
          let univs ← lvls.mapM $ toYatimaUniv levelParams
          let univsCids ← univs.mapM univToCid
          (univsCids.zip univs).forM fun (univCid, univ) =>
            addToEnv $ .univ_cache univCid univ
          return .const nam constId univsCids
        | none => throw s!"Unknown constant '{nam}'"
    | .app fnc arg _ => do
      let fnc ← toYatimaExpr levelParams fnc
      let arg ← toYatimaExpr levelParams arg
      return .app fnc arg
    | .lam nam bnd bod _ => do
      let bndInfo := bnd.binderInfo
      let bnd ← toYatimaExpr levelParams bnd
      incrNBinders
      let bod ← toYatimaExpr levelParams bod
      return .lam nam bndInfo bnd bod
    | .forallE nam dom img _ => do
      let bndInfo := dom.binderInfo
      let dom ← toYatimaExpr levelParams dom
      incrNBinders
      let img ← toYatimaExpr levelParams img
      return .pi nam bndInfo dom img
    | .letE nam typ exp bod _ => do
      let typ ← toYatimaExpr levelParams typ
      incrNBinders
      let exp ← toYatimaExpr levelParams exp
      let bod ← toYatimaExpr levelParams bod
      return .letE nam typ exp bod
    | .lit lit _ => return .lit lit
    | .mdata _ e _ => toYatimaExpr levelParams e
    | .proj _ idx exp _ => do
      let exp ← toYatimaExpr levelParams exp
      return .proj idx exp
    | .fvar .. => throw "Free variable found"
    | .mvar .. => throw "Metavariable found"

  partial def toYatimaConst : Lean.ConstantInfo → ToYatimaM Const
    | .axiomInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      return .axiom {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        safe := not struct.isUnsafe }
    | .thmInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      let value ← toYatimaExpr struct.levelParams struct.value
      let valueCid ← exprToCid value
      addToEnv $ .expr_cache valueCid value
      return .theorem {
        name  := struct.name
        lvls  := struct.levelParams.map .ofLeanName
        type  := typeCid
        value := valueCid }
    | .opaqueInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      let value ← toYatimaExpr struct.levelParams struct.value
      let valueCid ← exprToCid value
      addToEnv $ .expr_cache valueCid value
      return .opaque {
        name  := struct.name
        lvls  := struct.levelParams.map .ofLeanName
        type  := typeCid
        value := valueCid
        safe  := not struct.isUnsafe }
    | .defnInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      let value ← toYatimaExpr struct.levelParams struct.value
      let valueCid ← exprToCid value
      addToEnv $ .expr_cache valueCid value
      return .definition {
        name   := struct.name
        lvls   := struct.levelParams.map .ofLeanName
        type   := typeCid
        value  := valueCid
        safety := struct.safety }
    | .ctorInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      match (← read).find? struct.induct with
      | some leanConst =>
        let const ← toYatimaConst leanConst
        let constId ← constToCid const
        addToEnv $ .const_cache constId const
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
      addToEnv $ .expr_cache typeCid type
      let ctors : List (Name × ExprCid) ← struct.ctors.mapM
        fun nam => do match (← read).find?' nam with
          | some leanConst =>
            set { (← get) with constSubst := some struct.name }
            let type ← toYatimaExpr struct.levelParams leanConst.type
            let typeCid ← exprToCid type
            addToEnv $ .expr_cache typeCid type
            return (nam, typeCid)
          | none => throw s!"Unknown constant '{nam}'"
      return .inductive {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        params := struct.numParams
        indices := struct.numIndices
        ctors := ctors
        recr := struct.isRec
        refl := struct.isReflexive
        nest := struct.isNested
        safe := not struct.isUnsafe }
    | .recInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      let inductName := struct.getInduct
      match (← read).find? inductName with
      | some leanConst =>
        let const ← toYatimaConst leanConst
        let constId ← constToCid const
        addToEnv $ .const_cache constId const
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
      addToEnv $ .expr_cache typeCid type
      return .quotient {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        kind := struct.kind }

end

def buildEnv (constMap : Lean.ConstMap) : ToYatimaM Env := do
  constMap.forM fun _ leanConst => do
    let yatimaConst ← toYatimaConst leanConst
    let constCid ← constToCid yatimaConst
    addToEnv $ .const_cache constCid yatimaConst
  return (← get).env

def extractEnv (constMap : Lean.ConstMap) : Except String Env :=
  ToYatimaM.run constMap default (buildEnv constMap)

end Yatima.Compiler.FromLean
