import Yatima.Compiler.Printing
import Yatima.ToIpld

import Lean

namespace Yatima.Compiler

instance : Coe Lean.Name Name where
  coe := .ofLeanName

instance : Coe (List Lean.Name) (List Name) where
  coe l := l.map .ofLeanName

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

inductive YatimaStoreEntry
  | univ_cache  : UnivCid      → Univ      → YatimaStoreEntry
  | univ_anon   : UnivAnonCid  → UnivAnon  → YatimaStoreEntry
  | univ_meta   : UnivMetaCid  → UnivMeta  → YatimaStoreEntry
  | expr_cache  : ExprCid      → Expr      → YatimaStoreEntry
  | expr_anon   : ExprAnonCid  → ExprAnon  → YatimaStoreEntry
  | expr_meta   : ExprMetaCid  → ExprMeta  → YatimaStoreEntry
  | const_cache : ConstCid     → Const     → YatimaStoreEntry
  | const_anon  : ConstAnonCid → ConstAnon → YatimaStoreEntry
  | const_meta  : ConstMetaCid → ConstMeta → YatimaStoreEntry

def addToStore (y : YatimaStoreEntry) : CompileM Unit := do
  let stt ← get
  let store := stt.store
  match y with
  | .univ_cache  cid obj => set { stt with store := { store with univ_cache  := store.univ_cache.insert cid obj  } }
  | .univ_anon   cid obj => set { stt with store := { store with univ_anon   := store.univ_anon.insert cid obj   } }
  | .univ_meta   cid obj => set { stt with store := { store with univ_meta   := store.univ_meta.insert cid obj   } }
  | .expr_cache  cid obj => set { stt with store := { store with expr_cache  := store.expr_cache.insert cid obj  } }
  | .expr_anon   cid obj => set { stt with store := { store with expr_anon   := store.expr_anon.insert cid obj   } }
  | .expr_meta   cid obj => set { stt with store := { store with expr_meta   := store.expr_meta.insert cid obj   } }
  | .const_cache cid obj => set { stt with store := { store with const_cache := store.const_cache.insert cid obj } }
  | .const_anon  cid obj => set { stt with store := { store with const_anon  := store.const_anon.insert cid obj  } }
  | .const_meta  cid obj => set { stt with store := { store with const_meta  := store.const_meta.insert cid obj  } }

open ToIpld

def univToCid (u : Univ) : CompileM UnivCid := do
  let univAnon : UnivAnon := u.toAnon
  let univAnonCid : UnivAnonCid := univAnonToCid univAnon
  addToStore $ .univ_anon univAnonCid univAnon
  let univMeta : UnivMeta := u.toMeta
  let univMetaCid : UnivMetaCid := univMetaToCid univMeta
  addToStore $ .univ_meta univMetaCid univMeta
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
    addToStore $ .expr_anon exprAnonCid exprAnon
    let exprMetaCid : ExprMetaCid := exprMetaToCid exprMeta
    addToStore $ .expr_meta exprMetaCid exprMeta
    return ⟨exprAnonCid, exprMetaCid⟩

end

def constToCid (c : Const) : CompileM ConstCid := do
  let constAnon : ConstAnon := c.toAnon
  let constAnonCid : ConstAnonCid := constAnonToCid constAnon
  addToStore $ .const_anon constAnonCid constAnon
  let constMeta : ConstMeta := c.toMeta
  let constMetaCid : ConstMetaCid := constMetaToCid constMeta
  addToStore $ .const_meta constMetaCid constMeta
  return ⟨constAnonCid, constMetaCid⟩

def toYatimaUniv : Lean.Level → CompileM Univ
  | .zero _      => return .zero
  | .succ n _    => do
    let univ ← toYatimaUniv n
    let univCid ← univToCid univ
    addToStore $ .univ_cache univCid univ
    return .succ univCid
  | .max  a b _  => do
    let univA ← toYatimaUniv a
    let univACid ← univToCid univA
    addToStore $ .univ_cache univACid univA
    let univB ← toYatimaUniv b
    let univBCid ← univToCid univB
    addToStore $ .univ_cache univBCid univB
    return .max univACid univBCid
  | .imax a b _  => do
    let univA ← toYatimaUniv a
    let univACid ← univToCid univA
    addToStore $ .univ_cache univACid univA
    let univB ← toYatimaUniv b
    let univBCid ← univToCid univB
    addToStore $ .univ_cache univBCid univB
    return .imax univACid univBCid
  | .param name _ => do
    let lvls := (← read).univCtx
    match lvls.indexOf name with
    | some n => return .param name n
    | none   => throw s!"'{name}' not found in '{lvls}'"
  | .mvar .. => throw "Unfilled level metavariable"

instance : HMul Ordering Ordering Ordering where
  hMul
  | .gt, _ => .gt
  | .lt, _ => .lt
  | .eq, x => x

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

def findRecursorIn (recName : Name) (indInfos : List InductiveInfo) :
    Option (Nat × Nat × Bool) := Id.run do
  for (i, indInfo) in indInfos.enum do
    for (j, intRec) in indInfo.internalRecrs.enum do
      if recName == intRec.name then
        return (i, j, true)
    for (j, extRec) in indInfo.externalRecrs.enum do
      if recName == extRec.name then
        return (i, j, false)
  return none

mutual

  partial def toYatimaInternalRecRule
    (ctors : List Lean.Name) (rule : Lean.RecursorRule) :
      CompileM InternalRecursorRule := do
    match ctors.indexOf rule.ctor with
    | some idx =>
      let type ← toYatimaExpr none rule.rhs
      let typeCid ← exprToCid type
      addToStore $ .expr_cache typeCid type
      return { ctor := idx, fields := rule.nfields, rhs := typeCid }
    | none => throw s!"'{rule.ctor}' not found in '{ctors}'"

  partial def toYatimaExternalRecRule (rule : Lean.RecursorRule) :
      CompileM ExternalRecursorRule := do
    let type ← toYatimaExpr none rule.rhs
    let typeCid ← exprToCid type
    addToStore $ .expr_cache typeCid type
    match (← read).constMap.find?' rule.ctor with
    | some const =>
      let (_, ctorCid) ← processYatimaConst const
      return { ctor := ctorCid, fields := rule.nfields, rhs := typeCid }
    | none => throw s!"Unknown constant '{rule.ctor}'"

  partial def toYatimaInternalRec (ctors : List Lean.Name) (name: Lean.Name) :
      Lean.ConstantInfo → CompileM InternalRecursorInfo
    | .recInfo rec => do
      withResetCompileEnv rec.levelParams do
      let type ← Expr.fix name <$> toYatimaExpr (some name) rec.type
      let typeCid ← exprToCid type
      addToStore $ .expr_cache typeCid type
      let rules ← rec.rules.mapM $ toYatimaInternalRecRule ctors
      return {
        name := rec.name
        type := typeCid
        params := rec.numParams
        indices := rec.numIndices
        motives := rec.numMotives
        minors := rec.numMinors
        rules := rules
        k := rec.k }
    | const => throw s!"Invalid constant kind for '{const.name}'. Expected 'recursor' but got '{const.ctorName}'"

  partial def toYatimaExternalRec (name: Lean.Name) :
      Lean.ConstantInfo → CompileM ExternalRecursorInfo
    | .recInfo rec => do
      withResetCompileEnv rec.levelParams do
      let type ← Expr.fix name <$> toYatimaExpr (some name) rec.type
      let typeCid ← exprToCid type
      addToStore $ .expr_cache typeCid type
      let rules ← rec.rules.mapM toYatimaExternalRecRule
      return {
        name := rec.name
        type := typeCid
        params := rec.numParams
        indices := rec.numIndices
        motives := rec.numMotives
        minors := rec.numMinors
        rules := rules
        k := rec.k }
    | const => throw s!"Invalid constant kind for '{const.name}'. Expected 'recursor' but got '{const.ctorName}'"

  partial def toYatimaExpr (recr : Option Name) : Lean.Expr → CompileM Expr
    | .bvar idx _ => do
      let name ← match (← read).bindCtx.get? idx with
      | some name => pure name
      | none => throw "Processed bvar has index greater than length of binder context"
      return .var s!"{name}" idx
    | .sort lvl _ => do
      let univ ← toYatimaUniv lvl
      let univCid ← univToCid univ
      addToStore $ .univ_cache univCid univ
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
              addToStore $ .univ_cache univCid univ
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

  partial def toYatimaDef (isMutual : Bool) (defn : Lean.DefinitionVal) :
      CompileM Definition := do
    let type ← toYatimaExpr none defn.type
    let typeCid ← exprToCid type
    addToStore $ .expr_cache typeCid type
    let value := 
      if isMutual then ← toYatimaExpr none defn.value 
      else ← Expr.fix defn.name <$> toYatimaExpr (some defn.name) defn.value
    let valueCid ← exprToCid value
    addToStore $ .expr_cache valueCid value
    return {
      name   := defn.name
      lvls   := defn.levelParams
      type   := typeCid
      value  := valueCid
      safety := defn.safety }

  partial def toYatimaInductiveInfo (ind : Lean.InductiveVal) :
      CompileM InductiveInfo := do
    let type ← toYatimaExpr none ind.type
    let typeCid ← exprToCid type
    addToStore $ .expr_cache typeCid type
    let ctors : List ConstructorInfo ← ind.ctors.mapM
      fun name => do match (← read).constMap.find?' name with
        | some (.ctorInfo ctor) =>
          let type ← Expr.fix ind.name <$> toYatimaExpr (some ind.name) ctor.type
          let typeCid ← exprToCid type
          addToStore $ .expr_cache typeCid type
          return {
            name   := ctor.name
            type   := typeCid
            params := ctor.numParams
            fields := ctor.numFields }
        | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'constructor' but got '{const.ctorName}'"
        | none => throw s!"Unknown constant '{name}'"
    let leanRecs := (← read).constMap.childrenOfWith ind.name -- reverses once
      fun c => match c with | .recInfo _ => true | _ => false
    let (internalLeanRecs, externalLeanRecs)  ←
        leanRecs.foldlM (init := ([], [])) fun (accI, accE) r =>
        match r with
        | .recInfo rv => 
          if ind.all == rv.all then 
            return (r :: accI, accE)
          else
            return (accI, r :: accE)
        | _ => throw s!"Non-recursor {r.name} extracted from children"
    return {
      name := ind.name
      lvls := ind.levelParams
      type := typeCid
      params := ind.numParams
      indices := ind.numIndices
      ctors := ctors
      internalRecrs := ← internalLeanRecs.mapM $ toYatimaInternalRec ind.ctors ind.name
      externalRecrs := ← externalLeanRecs.mapM $ toYatimaExternalRec ind.name
      recr := ind.isRec
      refl := ind.isReflexive
      safe := not ind.isUnsafe }

  partial def buildInductiveInfoList (ind : Lean.InductiveVal) :
      CompileM $ List InductiveInfo := do
    let indInfos : List InductiveInfo ← ind.all.mapM fun name => do
      match (← read).constMap.find? name with
      | some (.inductInfo ind) => toYatimaInductiveInfo ind
      | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"
      | none => throw s!"Unknown constant '{name}'"
    return indInfos

  partial def toYatimaConst (const : Lean.ConstantInfo) :
      CompileM Const := withResetCompileEnv const.levelParams do
    match const with
    | .axiomInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToStore $ .expr_cache typeCid type
      return .axiom {
        name := struct.name
        lvls := struct.levelParams
        type := typeCid
        safe := not struct.isUnsafe }
    | .thmInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToStore $ .expr_cache typeCid type
      let value ← Expr.fix struct.name <$> toYatimaExpr (some struct.name) struct.value
      let valueCid ← exprToCid value
      addToStore $ .expr_cache valueCid value
      return .theorem {
        name  := struct.name
        lvls  := struct.levelParams
        type  := typeCid
        value := valueCid }
    | .opaqueInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToStore $ .expr_cache typeCid type
      let value ← Expr.fix struct.name <$> toYatimaExpr (some struct.name) struct.value
      let valueCid ← exprToCid value
      addToStore $ .expr_cache valueCid value
      return .opaque {
        name  := struct.name
        lvls  := struct.levelParams
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
        let mutualDefs ← sortDefs [mutualDefs]
        for (i, ds) in mutualDefs.enum do
          for d in ds do 
            set { ← get with mutIdx := (← get).mutIdx.insert d.name i }
        let definitions ← withOrder mutualNames $ 
          mutualDefs.mapM fun ds => ds.mapM $ toYatimaDef true
        return .mutDefBlock ⟨definitions⟩
      | none => return .definition $ ← toYatimaDef false struct 
    | .ctorInfo struct =>
      let type ← Expr.fix struct.induct <$> toYatimaExpr (some struct.induct) struct.type
      let typeCid ← exprToCid type
      addToStore $ .expr_cache typeCid type
      match (← read).constMap.find? struct.induct with
      | some const@(.inductInfo ind) =>
        let name := struct.name
        let indidx ← (match ind.all.indexOf ind.name with
          | some i => return i
          | none => throw s!"Inductive not present in its mutual block")
        match ind.ctors.indexOf name with
        | some idx =>
          let indInfos ← buildInductiveInfoList ind
          let indBlock : Const := .indBlock indInfos
          let indBlockCid ← constToCid indBlock
          return .constructor {
            name  := name
            lvls  := struct.levelParams
            type  := typeCid
            block := indBlockCid
            ind   := indidx
            idx   := struct.cidx }
        | none => throw s!"'{name}' wasn't found as a constructor for the inductive '{ind.name}'"
      | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"
      | none => throw s!"Unknown constant '{struct.induct}'"
    | .inductInfo struct =>
      let indInfos ← buildInductiveInfoList struct
      let indBlock : Const := .indBlock indInfos
      let indBlockCid ← constToCid indBlock
      addToStore $ .const_cache indBlockCid indBlock
      let mut ind : Option Const := none
      for (idx, name) in struct.all.enum do
        match (← read).constMap.find? name with
        | some const => 
          let type ← toYatimaExpr none const.type
          let typeCid ← exprToCid type
          addToStore $ .expr_cache typeCid type
          let const := Const.inductive {
            name := name
            lvls := const.levelParams
            type := typeCid
            block := indBlockCid
            ind := idx }
          let constCid ← constToCid const
          addToStore $ .const_cache constCid const
          set { ← get with cache := (← get).cache.insert name const }
          if name == struct.name then ind := some const
        | none   => throw s!"Unknown constant '{name}'"
      match ind with
      | some ind' => return ind'
      | none => throw s!"Constant for '{struct.name}' wasn't compiled"
    | .recInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToStore $ .expr_cache typeCid type
      let inductName := struct.getInduct
      match (← read).constMap.find? inductName with
      | some (.inductInfo ind) =>
        let indInfos ← buildInductiveInfoList ind
        let indBlock : Const := .indBlock indInfos
        let indBlockCid ← constToCid indBlock
        addToStore $ .const_cache indBlockCid indBlock
        match findRecursorIn struct.name indInfos with
        | some (ind, idx, intern) =>
          return .recursor {
            name   := struct.name
            lvls   := struct.levelParams
            type   := typeCid
            block  := indBlockCid
            ind    := ind
            idx    := idx
            intern := intern }
        | none => throw s!"Recursor '{struct.name}' not found as a recursor of '{inductName}'"
      | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"
      | none => throw s!"Unknown constant '{inductName}'"
    | .quotInfo struct =>
      let type ← toYatimaExpr none struct.type
      let typeCid ← exprToCid type
      addToStore $ .expr_cache typeCid type
      return .quotient {
        name := struct.name
        lvls := struct.levelParams
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
  partial def processYatimaConst (const : Lean.ConstantInfo) :
      CompileM $ Const × ConstCid := do
    match (← get).cache.find? const.name with
    | none =>
      let name := const.name
      let const ← toYatimaConst const
      let constCid ← constToCid const
      addToStore $ .const_cache constCid const
      set { ← get with cache := (← get).cache.insert const.name const }
      match (← get).mutIdx.find? name with
      | some i =>
        match const.lvlsAndType with
        | some (lvls, type) =>
          let mutConst := .mutDef ⟨name, lvls, type, constCid, i⟩
          let mutCid ← constToCid mutConst
          addToStore $ .const_cache mutCid mutConst
          set { ← get with cache := (← get).cache.insert name mutConst }
          pure (mutConst, mutCid)
        | none => throw "Invalid nested mutual block"
      | none => pure (const, constCid)
    | some const => pure (const, ← constToCid const)
 
  partial def cmpExpr (names : Std.RBMap Lean.Name Nat compare) :
      Lean.Expr → Lean.Expr → CompileM Ordering
    | .mvar .., _ => throw "Unfilled expr metavariable"
    | _, .mvar .. => throw "Unfilled expr metavariable"
    | .fvar .., _ => throw "expr free variable"
    | _, .fvar .. => throw "expr free variable"
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
      match names.find? x, names.find? y with
      | some nx, some ny => return compare nx ny
      | none, some ny => return .gt
      | some nx, none => return .lt
      | none, none => do
        match (← read).constMap.find?' x, (← read).constMap.find?' y with
        | some xConst, some yConst => do
          let xCid := (← processYatimaConst xConst).snd
          let yCid := (← processYatimaConst yConst).snd
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
    (names : Std.RBMap Lean.Name Nat compare) (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) :
      CompileM Ordering := do
    let ls := compare x.levelParams.length y.levelParams.length
    let ts ← cmpExpr names x.type y.type
    let vs ← cmpExpr names x.value y.value
    return concatOrds [ls, ts, vs]

  partial def eqDef
    (names : Std.RBMap Lean.Name Nat compare) (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) :
      CompileM Bool := do
    match (← cmpDef names x y )with 
      | .eq => pure true 
      | _ => pure false

  /--  -/
  partial def sortDefs (dss : List (List Lean.DefinitionVal)) : 
      CompileM (List (List Lean.DefinitionVal)) := do
    let enum (ll : List (List Lean.DefinitionVal)) := 
      Std.RBMap.ofList $ (ll.enum.map fun (n, xs) => xs.map (·.name, n)).join
    let names := enum dss
    let newDss ← (← dss.mapM fun ds => 
      match ds with 
      | [] => unreachable! -- should never occur
      | [d] => return [[d]]
      | ds => do return (← List.groupByM (eqDef names) $ ← ds.sortByM (cmpDef names))).joinM
    let newNames := enum newDss
    
    -- must normalize, see comments
    let normDss := dss.map fun ds => List.sort $ ds.map (·.name)
    let normNewDss := newDss.map fun ds => List.sort $ ds.map (·.name)
    if normDss == normNewDss then 
      return newDss
    else 
      sortDefs newDss

end

def printCompilationStats : CompileM Unit := do
  dbg_trace "\nCompilation stats:"
  dbg_trace s!"univ_cache size: {(← get).store.univ_cache.size}"
  dbg_trace s!"expr_cache size: {(← get).store.expr_cache.size}"
  dbg_trace s!"const_cache size: {(← get).store.const_cache.size}"
  dbg_trace s!"constMap size: {(← read).constMap.size}"
  dbg_trace s!"cache size: {(← get).cache.size}"
  dbg_trace s!"cache: {(← get).cache.toList.map fun (n, c) => (n, c.ctorName)}"

open PrintLean PrintYatima in
def buildStore (constMap : Lean.ConstMap)
    (printLean : Bool) (printYatima : Bool) : CompileM Store := do
  constMap.forM fun name const => do
    if printLean || printYatima then
      dbg_trace "\n========================================="
      dbg_trace s!"Processing: {name}"
      dbg_trace "========================================="
    if printLean then
      dbg_trace "------------- Lean constant -------------"
      dbg_trace s!"{printLeanConst const}"
    let (const, constCid) ← processYatimaConst const
    if printYatima then
      dbg_trace "------------ Yatima constant ------------"
      dbg_trace s!"{← printYatimaConst const}"
      dbg_trace s!"Anon CID: {constCid.anon.data}"
      dbg_trace s!"Meta CID: {constCid.meta.data}"
  printCompilationStats
  return (← get).store

def extractEnv (map map₀ : Lean.ConstMap) (printLean printYatima : Bool) :
    Except String Store :=
  let map  := Lean.filterConstants map
  let map₀ := Lean.filterConstants map₀
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
      (buildStore delta printLean printYatima)
  | .error e => throw e

def runFrontend (code fileName : String) (printLean printYatima : Bool) :
    IO $ Except String Store := do
  Lean.initSearchPath $ ← Lean.findSysroot
  let (env, ok) ← Lean.Elab.runFrontend code .empty fileName default
  if ok then
    let (env₀, _) ← Lean.Elab.runFrontend default .empty default default
    match extractEnv env.constants env₀.constants printLean printYatima with
    | .ok store => return .ok store
    | .error e => return .error e
  else
    return .error s!"Lean frontend failed on file {fileName}"

end Yatima.Compiler
