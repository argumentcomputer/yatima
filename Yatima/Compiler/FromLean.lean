import Yatima.Compiler.Graph
import Yatima.Compiler.Printing
import Yatima.Compiler.LeanTypesUtils
import Yatima.Utils
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
    | .var name n => return (.var n, .var name)
    | .sort u    => return (.sort u.anon, .sort u.meta)
    | .const name c ls =>
      return (.const c.anon $ ls.map (·.anon),
        .const name c.meta $ ls.map (·.meta))
    | .app fnc arg => do
      let fncCid ← exprToCid fnc
      let argCid ← exprToCid arg
      return (.app fncCid.anon argCid.anon, .app fncCid.meta argCid.meta)
    | .lam name bnd typ bod => do
      let typCid ← exprToCid typ
      let bodCid ← exprToCid bod
      return (.lam typCid.anon bodCid.anon,
        .lam name bnd typCid.meta bodCid.meta)
    | .pi name bnd dom img => do
      let domCid ← exprToCid dom
      let imgCid ← exprToCid img
      return (.pi domCid.anon imgCid.anon,
        .pi name bnd domCid.meta imgCid.meta)
    | .letE name typ exp bod => do
      let typCid ← exprToCid typ
      let expCid ← exprToCid exp
      let bodCid ← exprToCid bod
      return (
        .letE typCid.anon expCid.anon bodCid.anon, 
        .letE name typCid.meta expCid.meta bodCid.meta
      )
    | .lit lit => return (.lit lit, .lit)
    | .lty lty => return (.lty lty, .lty)
    | .fix name exp => do
      let expCid ← exprToCid exp
      return (.fix expCid.anon, .fix name expCid.meta)
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
  | .param name _ => do
    let lvls := (← read).univCtx
    match lvls.indexOf name with
    | some n => return .param name n
    | none   => throw s!"'{name}' not found in '{lvls}'"
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

  partial def toYatimaRecursorRule
    (ctorCid : ConstCid) (name: Lean.Name) (rules : Lean.RecursorRule) :
      CompileM RecursorRule := do
    let rhs ← toYatimaExpr (some name) rules.rhs
    let rhsCid ← exprToCid rhs
    addToEnv $ .expr_cache rhsCid rhs
    return ⟨ctorCid, rules.nfields, rhsCid⟩

  partial def toYatimaExpr (recr : Option Name) : Lean.Expr → CompileM Expr
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
    | .const name lvls _ => do
      if recr == some name then
        return .var name (← read).bindCtx.length
      else match (← read).order.indexOf name with
        | some i => return .var name $ (← read).bindCtx.length + i
        | none   => match (← read).constMap.find?' name with
          | some const => do
            let (const, constCid) ← processYatimaConst const
            let univs ← lvls.mapM $ toYatimaUniv
            let univsCids ← univs.mapM univToCid
            (univsCids.zip univs).forM fun (univCid, univ) =>
              addToEnv $ .univ_cache univCid univ
            return .const name constCid univsCids
          | none => throw s!"Unknown constant '{name}'"
    | .app fnc arg _ => .app <$> (toYatimaExpr recr fnc) <*> (toYatimaExpr recr arg)
    | .lam name typ bod _ => .lam name typ.binderInfo <$> (toYatimaExpr recr typ) <*> (withName name $ toYatimaExpr recr bod)
    | .forallE name dom img _ => .pi name dom.binderInfo <$> (toYatimaExpr recr dom) <*> (withName name $ toYatimaExpr recr img)
    | .letE name typ exp bod _ => .letE name <$> (toYatimaExpr recr typ) <*> (toYatimaExpr recr exp) <*> (withName name $ toYatimaExpr recr bod)
    | .lit lit _ => return .lit lit
    | .mdata _ e _ => toYatimaExpr recr e
    | .proj _ idx exp _ => .proj idx <$> toYatimaExpr recr exp
    | .fvar .. => throw "Free variable found"
    | .mvar .. => throw "Metavariable found"

  partial def toYatimaDef (defn : Lean.DefinitionVal) : CompileM Definition := do
    let type ← toYatimaExpr none defn.type
    let typeCid ← exprToCid type
    addToEnv $ .expr_cache typeCid type
    let value ← Expr.fix defn.name <$> toYatimaExpr (some defn.name) defn.value
    let valueCid ← exprToCid value
    addToEnv $ .expr_cache valueCid value
    return {
      name   := defn.name
      lvls   := defn.levelParams.map .ofLeanName
      type   := typeCid
      value  := valueCid
      safety := defn.safety }

  partial def toYatimaConst (const : Lean.ConstantInfo) :
      CompileM Const := withResetCompileEnv const.levelParams do
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
          | _ => throw "Non-def constant found in a mutual block of definitions"
        let (mutualDefs, mutualNames) ← sortDefs mutualDefs
        let mut i := 0
        for name in mutualNames do
          set { ← get with mutIdx := (← get).mutIdx.insert name i }
          i := i + 1
        let definitions ← withOrder mutualNames $ mutualDefs.mapM toYatimaDef
        return .mutBlock ⟨definitions⟩
      | none => return .definition $ ← toYatimaDef struct
    | .ctorInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToEnv $ .expr_cache typeCid type
      match (← read).constMap.find? struct.induct with
      | some leanConst =>
        let (const, constCid) ← processYatimaConst leanConst
        return .constructor {
          name := struct.name
          lvls := struct.levelParams.map .ofLeanName
          type := typeCid
          ind  := constCid
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
        fun name => do match (← read).constMap.find?' name with
          | some leanConst => return (name, leanConst.type)
          | none => throw s!"Unknown constant '{name}'"
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
        let (const, cid) ← processYatimaConst leanConst
        let rules ← struct.rules.mapM $ toYatimaRecursorRule cid struct.name
        return .recursor {
          name := struct.name
          lvls := struct.levelParams.map .ofLeanName
          type := typeCid
          params := struct.numParams
          ind := cid
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

  /-- 
  Process a Lean constant into a Yatima constant, returning both the Yatima
  constant and its cid.
  
  Different behavior is taken if the input `leanConst` is in a mutual block,
  since `toYatimaConst` returns the constant of the entire block (see
  `toYatimaConst`). We avoid returning the entire block and return the `mutDef`
  corresponding the input.

  Side effects: caches any new processed values in `cache`, `expr_cache`, and
  `const_cache`.
  -/
  partial def processYatimaConst (leanConst: Lean.ConstantInfo) :
      CompileM $ Const × ConstCid := do
    match (← get).cache.find? leanConst.name with
    | none =>
      let name := leanConst.name
      let const ← toYatimaConst leanConst
      let constCid ← constToCid const
      addToEnv $ .const_cache constCid const
      set { ← get with cache := (← get).cache.insert const.name const }
      match (← get).mutIdx.find? name with
      | some i => do
        let mutConst := .mutDef ⟨constCid, name, i⟩
        let mutCid ← constToCid mutConst
        addToEnv $ .const_cache mutCid mutConst
        set { ← get with cache := (← get).cache.insert name mutConst }
        pure (mutConst, mutCid)
      | none => pure (const, constCid)
    | some const => pure (const, ← constToCid const)
  
  partial def cmpExpr (names : List Lean.Name) :
      Lean.Expr → Lean.Expr → CompileM Ordering
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
        | some xConst, some yConst => do
          let xCid ← processYatimaConst xConst >>= constToCid ∘ Prod.fst
          let yCid ← processYatimaConst yConst >>= constToCid ∘ Prod.fst
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

  partial def cmpDef
    (names : List Lean.Name) (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) :
      CompileM Ordering := do
    let ls := compare x.levelParams.length y.levelParams.length
    let ts ← cmpExpr names x.type y.type
    let vs ← cmpExpr names x.value y.value
    return concatOrds [ls, ts, vs]

  partial def sortDefs (ds: List Lean.DefinitionVal) : 
      CompileM (List Lean.DefinitionVal × List Lean.Name) := do
    let names : List Lean.Name := ds.map (·.name)
    let res ← Utils.sortByM (cmpDef names) ds
    pure (res, res.map (·.name))

end

def printCompilationStats : CompileM Unit := do
  dbg_trace "\n\nCompilation stats:"
  dbg_trace s!"univ_cache size: {(← get).env.univ_cache.size}"
  dbg_trace s!"expr_cache size: {(← get).env.expr_cache.size}"
  dbg_trace s!"const_cache size: {(← get).env.const_cache.size}"
  dbg_trace s!"constMap size: {(← read).constMap.size}"
  dbg_trace s!"cache size: {(← get).cache.size}"
  dbg_trace s!"cache: {(← get).cache.toList.map fun (n, c) => (n, c.ctorName)}"

open PrintLean PrintYatima in
def buildEnv (constMap : Lean.ConstMap)
    (printLean : Bool) (printYatima : Bool) : CompileM Env := do
  constMap.forM fun name const => do
    if printLean || printYatima then dbg_trace s!"\nProcessing: {name}"
    if printLean then
      dbg_trace "------- Lean constant -------"
      dbg_trace s!"{printLeanConst const}"
    let (const, constCid) ← processYatimaConst const
    if printYatima then
      dbg_trace "------ Yatima constant ------"
      dbg_trace s!"{← printYatimaConst const}"
  printCompilationStats
  return (← get).env

open Yatima.LeanTypesUtils (filterConstants) in
def extractEnv (map map₀ : Lean.ConstMap) (printLean printYatima : Bool) :
    Except String Env :=
  let map  := filterConstants map
  let map₀ := filterConstants map₀
  let delta : Lean.ConstMap := map.fold
    (init := Lean.SMap.empty) fun acc n c =>
      match map₀.find? n with
      | some c' => if c == c' then acc else acc.insert n c
      | none    => acc.insert n c
  let g : Graph := Lean.referenceMap map
  match g.scc? with
  | .ok vss =>
    let nss : List (List $ Lean.Name × List Lean.Name) :=
      vss.map fun vs => 
        vs.map fun v => (v, vs)
    CompileM.run 
      ⟨map, [], [], Std.RBMap.ofList nss.join, []⟩
      default 
      (buildEnv delta printLean printYatima)
  | .error e => throw e

end Yatima.Compiler
