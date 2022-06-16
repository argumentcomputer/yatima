import Yatima.Graph.Graph
import Yatima.Compiler.Printing
import Yatima.Compiler.Utils
import Yatima.ToIpld

import Lean

namespace Yatima.Compiler

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

inductive YatimaEnvEntry
  | univ_cache  : UnivCid      → Univ      → YatimaEnvEntry
  | univ_anon   : UnivAnonCid  → UnivAnon  → YatimaEnvEntry
  | univ_meta   : UnivMetaCid  → UnivMeta  → YatimaEnvEntry
  | expr_cache  : ExprCid      → Expr      → YatimaEnvEntry
  | expr_anon   : ExprAnonCid  → ExprAnon  → YatimaEnvEntry
  | expr_meta   : ExprMetaCid  → ExprMeta  → YatimaEnvEntry
  | const_cache : ConstCid     → Const     → YatimaEnvEntry
  | const_anon  : ConstAnonCid → ConstAnon → YatimaEnvEntry
  | const_meta  : ConstMetaCid → ConstMeta → YatimaEnvEntry

def addToEnv (y : YatimaEnvEntry) : CompileM Unit := do
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

open ToIpld

def univToCid (u : Univ) : CompileM UnivCid := do
  let univAnon : UnivAnon := u.toAnon
  let univAnonCid : UnivAnonCid := univAnonToCid univAnon
  addToEnv $ .univ_anon univAnonCid univAnon
  let univMeta : UnivMeta := u.toMeta
  let univMetaCid : UnivMetaCid := univMetaToCid univMeta
  addToEnv $ .univ_meta univMetaCid univMeta
  return ⟨univAnonCid, univMetaCid⟩

mutual

  def separateExpr (e : Expr) : CompileM (ExprAnon × ExprMeta) :=
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

  def exprToCid (e : Expr) : CompileM ExprCid := do
    let (exprAnon, exprMeta) ← separateExpr e
    let exprAnonCid : ExprAnonCid := exprAnonToCid exprAnon
    addToEnv $ .expr_anon exprAnonCid exprAnon
    let exprMetaCid : ExprMetaCid := exprMetaToCid exprMeta
    addToEnv $ .expr_meta exprMetaCid exprMeta
    return ⟨exprAnonCid, exprMetaCid⟩

end

def constToCid (c : Const) : CompileM ConstCid := do
  let constAnon : ConstAnon := c.toAnon
  let constAnonCid : ConstAnonCid := constAnonToCid constAnon
  addToEnv $ .const_anon constAnonCid constAnon
  let constMeta : ConstMeta := c.toMeta
  let constMetaCid : ConstMetaCid := constMetaToCid constMeta
  addToEnv $ .const_meta constMetaCid constMeta
  return ⟨constAnonCid, constMetaCid⟩

def toYatimaUniv : Lean.Level → CompileM Univ
  | .zero _      => return .zero
  | .succ n _    => do
    let univ ← toYatimaUniv n
    let univCid ← univToCid univ
    addToEnv $ .univ_cache univCid univ
    return .succ univCid
  | .max  a b _  => do
    let univA ← toYatimaUniv a
    let univACid ← univToCid univA
    addToEnv $ .univ_cache univACid univA
    let univB ← toYatimaUniv b
    let univBCid ← univToCid univB
    addToEnv $ .univ_cache univBCid univB
    return .max univACid univBCid
  | .imax a b _  => do
    let univA ← toYatimaUniv a
    let univACid ← univToCid univA
    addToEnv $ .univ_cache univACid univA
    let univB ← toYatimaUniv b
    let univBCid ← univToCid univB
    addToEnv $ .univ_cache univBCid univB
    return .imax univACid univBCid
  | .param nam _ => do
    let lvls := (← read).univCtx
    match lvls.indexOf nam with
    | some n => return .param nam n
    | none   => throw s!"'{nam}' not found in '{lvls}'"
  | .mvar .. => throw "Unfilled level metavariable"

def concatOrds : List Ordering -> Ordering :=
  List.foldl (fun x y => x * y) .eq

def cmpLevel (x : Lean.Level) (y : Lean.Level) : (CompileM Ordering) := do
  match x, y with
  | .mvar .., _ => throw "Unfilled level metavariable"
  | _, .mvar .. => throw "Unfilled level metavariable"
  | .zero _, .zero _ => return .eq
  | .zero _, _ => return .lt
  | _, .zero _  => return .gt
  | .succ x _, .succ y _ => cmpLevel x y
  | .succ x _, _ => return .lt
  | _, .succ x _ => return .gt
  | .max lx ly _, .max rx ry _ => (· * ·) <$> cmpLevel lx rx <*> cmpLevel ly ry
  | .max _ _ _, _ => return .lt
  | _, .max _ _ _ => return .gt
  | .imax lx ly _, .imax rx ry _ => (· * ·) <$> cmpLevel lx rx <*> cmpLevel ly ry
  | .imax _ _ _, _ => return .lt
  | _, .imax _ _ _ => return .gt
  | .param x _, .param y _ => do
    let lvls := (← read).univCtx
    match (lvls.indexOf x), (lvls.indexOf y) with
      | some xi, some yi => return (compare xi yi)
      | none, _   => throw s!"'{x}' not found in '{lvls}'"
      | _, none   => throw s!"'{y}' not found in '{lvls}'"

mutual

  partial def toYatimaRecursorRule (ctorCid : ConstCid) (name: Lean.Name) (rules : Lean.RecursorRule) : CompileM RecursorRule := do
    let rhs ← toYatimaExpr (some name) rules.rhs
    let rhsCid ← exprToCid rhs
    addToEnv $ .expr_cache rhsCid rhs
    return ⟨ctorCid, rules.nfields, rhsCid⟩

  partial def toYatimaExpr (recr: Option Name): Lean.Expr → CompileM Expr
    | .bvar idx _ => do
      let name ← match (← read).bindCtx.get? idx with
      | some name => pure name
      | none => throw "Processed bvar has index greater than length of binder context"
      return .var s!"{name}" idx
    | .sort lvl _ => do
      let univ ← toYatimaUniv lvl
      let univCid ← univToCid univ
      addToEnv $ .univ_cache univCid univ
      return .sort univCid
    | .const nam lvls _ =>
      -- todo: also handle the case when `nam` is in a cycle
      if recr == some nam then
        return .var nam (← read).bindCtx.length
      else do
        match (← read).constMap.find?' nam with
          | some leanConst => do
            let const ← processYatimaConst leanConst
            let constId ← constToCid const
            addToEnv $ .const_cache constId const
            let univs ← lvls.mapM $ toYatimaUniv
            let univsCids ← univs.mapM univToCid
            (univsCids.zip univs).forM fun (univCid, univ) =>
              addToEnv $ .univ_cache univCid univ
            return .const nam constId univsCids
          | none => throw s!"Unknown constant '{nam}'"
    | .app fnc arg _ => .app <$> (toYatimaExpr recr fnc) <*> (toYatimaExpr recr arg)
    | .lam nam typ bod _ => .lam nam typ.binderInfo <$> (toYatimaExpr recr typ) <*> (withName nam $ toYatimaExpr recr bod)
    | .forallE nam dom img _ => .pi nam dom.binderInfo <$> (toYatimaExpr recr dom) <*> (withName nam $ toYatimaExpr recr img)
    | .letE nam typ exp bod _ => .letE nam <$> (toYatimaExpr recr typ) <*> (toYatimaExpr recr exp) <*> (withName nam $ toYatimaExpr recr bod)
    | .lit lit _ => return .lit lit
    | .mdata _ e _ => toYatimaExpr recr e
    | .proj _ idx exp _ => .proj idx <$> toYatimaExpr recr exp
    | .fvar .. => throw "Free variable found"
    | .mvar .. => throw "Metavariable found"

  partial def toYatimaDef (defn : Lean.DefinitionVal) : CompileM Definition := do
    let type ← toYatimaExpr none defn.type
    let typeCid ← exprToCid type
    addToEnv $ .expr_cache typeCid type
    -- todo: check if defn.name is in a cycle (via `CompileEnv.order`)
    let value ← Expr.fix defn.name <$> toYatimaExpr (some defn.name) defn.value
    let valueCid ← exprToCid value
    addToEnv $ .expr_cache valueCid value
    return {
      name   := defn.name
      lvls   := defn.levelParams.map .ofLeanName
      type   := typeCid
      value  := valueCid
      safety := defn.safety }

  partial def toYatimaConst (const: Lean.ConstantInfo) :
      CompileM Const := withLevelsAndResetBindCtx const.levelParams do
    match const with
    | .axiomInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      return .axiom {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        safe := not struct.isUnsafe }
    | .thmInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      let value ← Expr.fix struct.name <$> toYatimaExpr (some struct.name) struct.value
      let valueCid ← exprToCid value
      addToEnv $ .expr_cache valueCid value
      return .theorem {
        name  := struct.name
        lvls  := struct.levelParams.map .ofLeanName
        type  := typeCid
        value := valueCid }
    | .opaqueInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      let value ← Expr.fix struct.name <$> toYatimaExpr (some struct.name) struct.value
      let valueCid ← exprToCid value
      addToEnv $ .expr_cache valueCid value
      return .opaque {
        name  := struct.name
        lvls  := struct.levelParams.map .ofLeanName
        type  := typeCid
        value := valueCid
        safe  := not struct.isUnsafe }
    | .defnInfo struct =>
      -- figure out if we're in mutual definition
      match (← read).cycles.find? struct.name with 
      | some mutualNames =>
        let mutualDefs ← mutualNames.mapM fun name => do 
          match (← read).constMap.find? name with 
          | some (.defnInfo defn) => pure defn
          -- there shouldn't be anything else other than definitions here, so:
          | _ => unreachable!
        let mutualDefs ← sortDefs mutualDefs
        -- todo: fill this sorry with a hashmap of each name to its position in the cycle, starting from 0
        let definitions ← withOrder sorry $ mutualDefs.mapM toYatimaDef
        return .mutBlock ⟨definitions⟩
      | none => return .definition $ ← toYatimaDef struct
    | .ctorInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      match (← read).constMap.find? struct.induct with
      | some leanConst =>
        let const ← processYatimaConst leanConst
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
    | .inductInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      let ctors : List (Name × Lean.Expr) ← struct.ctors.mapM
        fun nam => do match (← read).constMap.find?' nam with
          | some leanConst => return (nam, leanConst.type)
          | none => throw s!"Unknown constant '{nam}'"
      let ctors : List (Name × ExprCid) ← ctors.mapM
        fun (nam, typ) => do
         let type ← toYatimaExpr (some struct.name) typ
         let typeCid ← exprToCid type
         addToEnv $ .expr_cache typeCid type
         return (nam, typeCid)
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
    | .recInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      let inductName := struct.getInduct
      match (← read).constMap.find? inductName with
      | some leanConst =>
        let const ← processYatimaConst leanConst
        let constId ← constToCid const
        addToEnv $ .const_cache constId const
        let rules ← struct.rules.mapM $ toYatimaRecursorRule constId struct.name
        return .recursor {
          name := struct.name
          lvls := struct.levelParams.map .ofLeanName
          type := typeCid
          params := struct.numParams
          ind := constId
          motives := struct.numMotives
          indices := struct.numIndices
          minors := struct.numMinors
          rules := rules
          k := struct.k
          safe := not struct.isUnsafe }
      | none => throw s!"Unknown constant '{inductName}'"
    | .quotInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      return .quotient {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        kind := struct.kind }

  partial def processYatimaConst (const: Lean.ConstantInfo) : CompileM Const := do
    let name : Name := const.name
    let cache := (← get).cache
    match cache.find? name with
    | none =>
      dbg_trace s!"[NOT IN CACHE YET] processing {name}"
      let const ← toYatimaConst const
      set { ← get with cache := cache.insert name const }
      pure const
    | some const =>
      -- dbg_trace s!"[ALREADY IN CACHE] processing {name}"
      pure const
  
  
  partial def cmpExpr (names : List Lean.Name) (x : Lean.Expr) (y : Lean.Expr) : CompileM Ordering := do
    match x, y with
    | .mvar .., _ => throw "Unfilled expr metavariable"
    | _, .mvar .. => throw "Unfilled expr metavariable"
    | .fvar .., _ => throw "expr free variable"
    | _, .fvar .. => throw "expr free metavariable"
    | .mdata _ x _, .mdata _ y _  => cmpExpr names x y
    | .mdata _ x _, y  => cmpExpr names x y
    | x, .mdata _ y _  => cmpExpr names x y
    | .bvar x _, .bvar y _ => return (compare x y)
    | .bvar _ _, _ => return .lt
    | _, .bvar _ _ => return .gt
    | .sort x _, .sort y _ => cmpLevel x y
    | .sort _ _, _ => return .lt
    | _, .sort _ _ => return .gt
    | .const x xls _, .const y yls _ => do
      let univs ← concatOrds <$> (List.zip xls yls).mapM (fun (x,y) => cmpLevel x y)
      if univs != .eq then return univs
      match names.contains x, names.contains y with
      | true, true => return .eq
      | false, true => return .gt
      | true, false => return .lt
      | false, false => do
        match (← read).constMap.find?' x, (← read).constMap.find?' y with
        | some x_const, some y_const => do
          let xCid ← processYatimaConst x_const >>= constToCid
          let yCid ← processYatimaConst y_const >>= constToCid
          return (compare xCid yCid)
        | none, some _ => throw s!"Unknown constant '{x}'"
        | some _, none => throw s!"Unknown constant '{y}'"
        | _, _ => throw s!"Unknown constants '{x}, {y}'"
    | .const _ _ _, _ => return .lt
    | _, .const _ _ _ => return .gt
    | .app xf xa _, .app yf ya _ => (· * ·) <$> cmpExpr names xf yf <*> cmpExpr names xa ya
    | .app _ _ _, _ => return .lt
    | _, .app _ _ _ => return .gt
    | .lam _ xt xb _, .lam _ yt yb _ => (· * ·) <$> cmpExpr names xt yt <*> cmpExpr names xb yb
    | .lam _ _ _ _, _ => return .lt
    | _, .lam _ _ _ _ => return .gt
    | .forallE _ xt xb _, .forallE _ yt yb _ => (· * ·) <$> cmpExpr names xt yt <*> cmpExpr names xb yb
    | .forallE _ _ _ _, _ => return .lt
    | _, .forallE _ _ _ _ => return .gt
    | .letE _ xt xv xb _, .letE _ yt yv yb _ => (· * · * ·) <$> cmpExpr names xt yt <*> cmpExpr names xv yv <*> cmpExpr names xb yb
    | .letE _ _ _ _ _, _ => return .lt
    | _, .letE _ _ _ _ _ => return .gt
    | .lit x _, .lit y _ =>
      return if x < y then .lt else if x == y then .eq else .gt
    | .lit _ _, _ => return .lt
    | _, .lit _ _ => return .gt
    | .proj _ nx tx _, .proj _ ny ty _ => do
      let ts ← cmpExpr names tx ty
      return concatOrds [ compare nx ny , ts ]

  partial def cmpDef (names : List Lean.Name) (x: Lean.DefinitionVal) (y: Lean.DefinitionVal) : CompileM Ordering := do
    let ls := compare x.levelParams.length y.levelParams.length
    let ts ← cmpExpr names x.type y.type
    let vs ← cmpExpr names x.value y.value
    return concatOrds [ls, ts, vs]

  partial def sortDefs (ds: List Lean.DefinitionVal): CompileM (List Lean.DefinitionVal) :=
    let names : List Lean.Name := ds.map (·.name)
    sortByM (cmpDef names) ds

end

open PrintLean PrintYatima in
def buildEnv (constMap : Lean.ConstMap)
    (printLean : Bool) (printYatima : Bool) : CompileM Env := do
  constMap.forM fun name const => do
    if name.toString.startsWith "QQQ" || name.toString.startsWith "WWW" then
      let env ← read
      let cache := (← get).cache
      let dbg := printLean || printYatima
      if dbg then dbg_trace s!"\nProcessing: {name}"
      if printLean then
        dbg_trace "------- Lean constant -------"
        dbg_trace s!"{printLeanConst const}"
      let const ← toYatimaConst const
      if printYatima then
        dbg_trace "------ Yatima constant ------"
        dbg_trace s!"{← printYatimaConst const}"
      addToEnv $ .const_cache (← constToCid const) const
  return (← get).env

def filterUnsafeConstants (cs : Lean.ConstMap) : Lean.ConstMap :=
  Lean.List.toSMap $ cs.toList.filter fun (_, c) => !c.isUnsafe

def extractEnv
  (constMap : Lean.ConstMap)
  (printLean : Bool)
  (printYatima : Bool)
    : Except String Env :=
  let map := filterUnsafeConstants constMap
  let g : Graph := Lean.referenceMap map
  match g.scc? with
  | .ok vss =>
    let nss : List (List $ Lean.Name × List Lean.Name) :=
      vss.map fun vs => 
        vs.map fun v => (v, vs)
    dbg_trace nss
    CompileM.run 
      ⟨map, [], [], Std.RBMap.ofList nss.join, .empty⟩
      default 
      (buildEnv map printLean printYatima)
  | .error e => throw e

end Yatima.Compiler
