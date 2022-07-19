import Yatima.Compiler.Printing
import Yatima.ToIpld
import YatimaStdLib.RBMap

import Lean

namespace Yatima.Compiler

open Std (RBMap)

instance : Coe Lean.Name Name where
  coe := toString

instance : Coe (List Lean.Name) (List Name) where
  coe l := l.map toString

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

open ToIpld

def toYatimaUniv (l : Lean.Level) : CompileM (UnivCid × Univ) := do
  let pair ← match l with
    | .zero _      => pure (zeroCid, .zero)
    | .succ n _    => do
      let (univCid, univ) ← toYatimaUniv n
      let cid := ⟨ univToCid (.succ univCid.anon), univToCid (.succ univCid.meta) ⟩
      pure (cid, .succ univ)
    | .max  a b _  => do
      let (univACid, univA) ← toYatimaUniv a
      let (univBCid, univB) ← toYatimaUniv b
      let cid := ⟨ univToCid (.max univACid.anon univBCid.anon), univToCid (.max univACid.meta univBCid.meta) ⟩
      pure (cid, .max univA univB)
    | .imax  a b _  => do
      let (univACid, univA) ← toYatimaUniv a
      let (univBCid, univB) ← toYatimaUniv b
      let cid := ⟨ univToCid (.imax univACid.anon univBCid.anon), univToCid (.imax univACid.meta univBCid.meta) ⟩
      pure (cid, .imax univA univB)
    | .param name _ => do
      let lvls := (← read).univCtx
      match lvls.indexOf? name with
      | some n => 
        let cid := ⟨ univToCid (.param () n), univToCid (.param name ()) ⟩
        pure (cid, .param name n)
      | none   => throw s!"'{name}' not found in '{lvls}'"
    | .mvar .. => throw "Unfilled level metavariable"
  addToStore pair
  pure pair

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
  | .succ _ _, _ => return .lt
  | _, .succ _ _ => return .gt
  | .max lx ly _, .max rx ry _ => (· * ·) <$> cmpLevel lx rx <*> cmpLevel ly ry
  | .max _ _ _, _ => return .lt
  | _, .max _ _ _ => return .gt
  | .imax lx ly _, .imax rx ry _ => (· * ·) <$> cmpLevel lx rx <*> cmpLevel ly ry
  | .imax _ _ _, _ => return .lt
  | _, .imax _ _ _ => return .gt
  | .param x _, .param y _ => do
    let lvls := (← read).univCtx
    match (lvls.indexOf? x), (lvls.indexOf? y) with
    | some xi, some yi => return (compare xi yi)
    | none, _   => throw s!"'{x}' not found in '{lvls}'"
    | _, none   => throw s!"'{y}' not found in '{lvls}'"

def findRecursorIn (recName : Name) (indInfos : List Inductive) :
    Option (Nat × Nat) := Id.run do
  for (i, indInfo) in indInfos.enum do
    for (j, intRec) in indInfo.recrs.enum do
      if recName == intRec.snd.name then
        return some (i, j)
  return none

def addFix (name : Name) : ExprCid × Expr → ExprCid × Expr
  | (bodyCid, body) =>
    let cid := ⟨ exprToCid $ .fix () bodyCid.anon, exprToCid $ .fix name bodyCid.meta ⟩
    (cid, .fix name body)

mutual

  partial def toYatimaConstructor (rule : Lean.RecursorRule) : CompileM Constructor := do
      let (rhsCid, rhs) ← toYatimaExpr rule.rhs
      addToStore (rhsCid, rhs)
      match (← read).constMap.find?' rule.ctor with
        | some (.ctorInfo ctor) =>
          let (typeCid, type) ← toYatimaExpr ctor.type
          addToStore (typeCid, type)
          return {
            rhs    := rhsCid
            lvls   := ctor.levelParams
            name   := ctor.name
            type   := typeCid
            params := ctor.numParams
            fields := ctor.numFields }
        | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'constructor' but got '{const.ctorName}'"
        | none => throw s!"Unknown constant '{rule.ctor}'"

  partial def toYatimaExternalRecRule (rule : Lean.RecursorRule) :
      CompileM RecursorRule := do
    let (rhsCid, rhs) ← toYatimaExpr rule.rhs
    addToStore (rhsCid, rhs)
    match (← read).constMap.find?' rule.ctor with
    | some const =>
      let (ctorCid, _) ← processYatimaConst const
      return { ctor := ctorCid, fields := rule.nfields, rhs := rhsCid }
    | none => throw s!"Unknown constant '{rule.ctor}'"

  partial def toYatimaInternalRec (ctors : List Lean.Name) :
      Lean.ConstantInfo → CompileM (Recursor .Intr × List Constructor)
    | .recInfo rec => do
      withLevels rec.levelParams do
        let (typeCid, type) ← toYatimaExpr rec.type
        addToStore (typeCid, type)
        let ctorMap : RBMap Name Constructor compare := ← rec.rules.foldlM (init := (RBMap.empty)) fun ctorMap r => do
          match ctors.indexOf? r.ctor with
          | some _ =>
            let ctor ← toYatimaConstructor r
            return ctorMap.insert ctor.name ctor
          -- this is an external recursor rule
          | none => return ctorMap
        let retCtors ← ctors.mapM fun ctor => do
          match ctorMap.find? ctor with
          | some thisCtor => pure thisCtor
          | none => unreachable!
        return ({
          name    := rec.name
          lvls    := rec.levelParams
          type    := typeCid
          params  := rec.numParams
          indices := rec.numIndices
          motives := rec.numMotives
          minors  := rec.numMinors
          rules   := ()
          k       := rec.k }, retCtors)
    | const => throw s!"Invalid constant kind for '{const.name}'. Expected 'recursor' but got '{const.ctorName}'"

  partial def toYatimaExternalRec :
      Lean.ConstantInfo → CompileM (Recursor .Extr)
    | .recInfo rec => do
      withLevels rec.levelParams do
        let (typeCid, type) ← toYatimaExpr rec.type
        addToStore (typeCid, type)
        let rules := ← rec.rules.foldlM (init := []) fun rules r => do
          let extRecrRule ← toYatimaExternalRecRule r
          return extRecrRule::rules
        return {
          name    := rec.name
          lvls    := rec.levelParams
          type    := typeCid
          params  := rec.numParams
          indices := rec.numIndices
          motives := rec.numMotives
          minors  := rec.numMinors
          rules   := rules
          k       := rec.k }
    | const => throw s!"Invalid constant kind for '{const.name}'. Expected 'recursor' but got '{const.ctorName}'"

  partial def toYatimaExpr (expr : Lean.Expr) : CompileM (ExprCid × Expr) := do
    let pair : ExprCid × Expr ← match expr with
      | .bvar idx _ => do
        let name ← match (← read).bindCtx.get? idx with
        | some name =>
          let cid := ⟨ exprToCid (.var () idx), exprToCid (.var name ()) ⟩
          pure (cid, .var name idx)
        | none => throw "Processed bvar has index greater than length of binder context"
      | .sort lvl _ => do
        let (univCid, univ) ← toYatimaUniv lvl
        let cid := ⟨ exprToCid (.sort univCid.anon), exprToCid (.sort univCid.meta) ⟩
        return (cid, .sort univ)
      | .const name lvls _ => do
        match (← read).recrCtx.find? name with
          | some i => 
            let idx := (← read).bindCtx.length + i
            let cid := ⟨ exprToCid (.var () idx), exprToCid (.var name ()) ⟩
            return (cid, .var name idx)
          | none   => match (← read).constMap.find?' name with
            | some const => do
              let (constCid, _) ← processYatimaConst const
              let pairs ← lvls.mapM $ toYatimaUniv
              let (univCids, univs) ← pairs.foldrM (fun pair pairs => pure (pair.fst :: pairs.fst, pair.snd :: pairs.snd)) ([], [])
              let cid := ⟨ exprToCid (.const () constCid.anon $ univCids.map UnivCid.anon)
                         , exprToCid (.const name constCid.meta $ univCids.map UnivCid.meta) ⟩
              return (cid, .const name constCid univs)
            | none => throw s!"Unknown constant '{name}'"
      | .app fnc arg _ => do
        let (fncCid, fnc) ← toYatimaExpr fnc
        let (argCid, arg) ← toYatimaExpr arg
        let cid := ⟨ exprToCid (.app fncCid.anon argCid.anon), exprToCid (.app fncCid.meta argCid.meta) ⟩
        return (cid, .app fnc arg)
      | .lam name typ bod data =>
        let (typCid, typ) ← toYatimaExpr typ
        let (bodCid, bod) ← withName name $ toYatimaExpr bod
        let bnd := data.binderInfo
        let cid := ⟨ exprToCid (.lam () bnd typCid.anon bodCid.anon), exprToCid (.lam name () typCid.meta bodCid.meta) ⟩
        return (cid, .lam name bnd typ bod)
      | .forallE name dom img data =>
        let (domCid, dom) ← toYatimaExpr dom
        let (imgCid, img) ← withName name $ toYatimaExpr img
        let bnd := data.binderInfo
        let cid := ⟨ exprToCid (.pi () bnd domCid.anon imgCid.anon), exprToCid (.pi name () domCid.meta imgCid.meta) ⟩
        return (cid, .pi name bnd dom img)
      | .letE name typ exp bod _ => 
        let (typCid, typ) ← toYatimaExpr typ
        let (expCid, exp) ← toYatimaExpr exp
        let (bodCid, bod) ← withName name $ toYatimaExpr bod
        let cid := ⟨ exprToCid (.letE () typCid.anon expCid.anon bodCid.anon), exprToCid (.letE name typCid.meta expCid.meta bodCid.meta) ⟩
        return (cid, .letE name typ exp bod)
      | .lit lit _ =>
        let cid := ⟨ exprToCid (.lit lit), exprToCid (.lit ()) ⟩
        return (cid, .lit lit)
      | .mdata _ e _ => toYatimaExpr e
      | .proj _ idx exp _ => do
        let (expCid, exp) ← toYatimaExpr exp
        let cid := ⟨ exprToCid (.proj idx expCid.anon), exprToCid (.proj () expCid.meta) ⟩
        return (cid, .proj idx exp)
      | .fvar .. => throw "Free variable found"
      | .mvar .. => throw "Metavariable found"
    addToStore pair
    pure pair

  partial def toYatimaDef (isMutual : Bool) (defn : Lean.DefinitionVal) :
      CompileM Definition := do
    let (typeCid, type) ← toYatimaExpr defn.type
    addToStore (typeCid, type)
    let (valueCid, value) ←
      if isMutual then toYatimaExpr defn.value
      else withRecrs (RBMap.single defn.name 0) $
        addFix defn.name <$> toYatimaExpr defn.value
    addToStore (valueCid, value)
    return {
      name   := defn.name
      lvls   := defn.levelParams
      type   := typeCid
      value  := valueCid
      safety := defn.safety }

  partial def isInternalRec (expr : Lean.Expr) (name : Lean.Name) : CompileM Bool :=
    match expr with
      | .forallE _ t e _  => match e with
        | .forallE ..  => isInternalRec e name
        -- t is the major premise
        | _ => isInternalRec t name
      | .app e .. => isInternalRec e name
      | .const n .. => return n == name
      | _ => return false

  partial def toYatimaInductive (ind : Lean.InductiveVal) :
      CompileM Inductive := do
    let (typeCid, type) ← toYatimaExpr ind.type
    addToStore (typeCid, type)
    -- reverses once
    let leanRecs := (← read).constMap.childrenOfWith ind.name
      fun c => match c with | .recInfo _ => true | _ => false
    let (recs, ctors) : (List (Sigma Recursor) × Option (List Constructor)) :=
      -- reverses again, keeping original order
      ← leanRecs.foldlM (init := ([], none)) fun (recs, ctors) r =>
        match r with
        | .recInfo rv => do
          if ← isInternalRec rv.type ind.name then do
            let (thisRec, thisCtors) := ← toYatimaInternalRec (ind.ctors) r
            return ((Sigma.mk .Intr thisRec) :: recs, some thisCtors)
          else do
            let thisRec := ← toYatimaExternalRec r
            return ((Sigma.mk .Extr thisRec) :: recs, ctors)
        | _ => throw s!"Non-recursor {r.name} extracted from children"
    let ctors := match ctors with
      | some ctors => ctors
      | none => unreachable!
    return {
      name     := ind.name
      lvls     := ind.levelParams
      type     := typeCid
      params   := ind.numParams
      indices  := ind.numIndices
      ctors    := ctors
      recrs    := recs
      recr     := ind.isRec
      refl     := ind.isReflexive
      safe     := not ind.isUnsafe }

  partial def buildInductiveInfoList (ind : Lean.InductiveVal) :
      CompileM $ List Inductive := do
    let mut funList : List Lean.Name := []
    for indName in ind.all do
      match (← read).constMap.find? indName with
      | some (.inductInfo ind) =>
        let leanRecs := (← read).constMap.childrenOfWith ind.name -- reverses once
          fun c => match c with | .recInfo _ => true | _ => false
        let leanRecs := leanRecs.map (·.name)
        funList := (funList.append ind.ctors).append leanRecs
      | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"
      | none => throw s!"Unknown constant '{indName}'"
    withRecrs (RBMap.enumList $ ind.all ++ funList) do
    let indInfos : List Inductive ← ind.all.mapM fun name => do
      match (← read).constMap.find? name with
      | some (.inductInfo ind) => toYatimaInductive ind
      | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"
      | none => throw s!"Unknown constant '{name}'"
    return indInfos

  partial def toYatimaConst (const : Lean.ConstantInfo) :
      CompileM (ConstCid × Const) := withResetCompileEnv const.levelParams do
    match const with
    | .axiomInfo struct =>
      let (typeCid, type) ← toYatimaExpr struct.type
      let ax := .axiom {
        name := struct.name
        lvls := struct.levelParams
        type := typeCid
        safe := not struct.isUnsafe }
      return (sorry, ax)
    | .thmInfo struct =>
      let (typeCid, type) ← toYatimaExpr struct.type
      withRecrs (RBMap.single struct.name 0) do
        let (valueCid, value) ← addFix struct.name <$> toYatimaExpr struct.value
        addToStore (valueCid, value)
        addToStoreAndCache $ .theorem {
          name  := struct.name
          lvls  := struct.levelParams
          type  := typeCid
          value := valueCid }
    | .opaqueInfo struct =>
      let (typeCid, type) ← toYatimaExpr struct.type
      withRecrs (RBMap.single struct.name 0) do
        let (valueCid, value) ← addFix struct.name <$> toYatimaExpr struct.value
        addToStore (valueCid, value)
        addToStoreAndCache $ .opaque {
          name  := struct.name
          lvls  := struct.levelParams
          type  := typeCid
          value := valueCid
          safe  := not struct.isUnsafe }
    | .quotInfo struct =>
      let (typeCid, type) ← toYatimaExpr struct.type
      addToStoreAndCache $ .quotient {
        name := struct.name
        lvls := struct.levelParams
        type := typeCid
        kind := struct.kind }
    | .defnInfo struct =>
      if struct.all.length == 1 then
        addToStoreAndCache $ .definition $ ← toYatimaDef false struct
      else
        let mutualDefs ← struct.all.mapM fun name => do
          match (← read).constMap.find? name with
          | some (.defnInfo defn) => pure defn
          | _ => throw s!"Unknown definition '{name}'"
        let mutualDefs ← sortDefs [mutualDefs]
        let mut mutualIdxs : RBMap Lean.Name Nat compare := RBMap.empty
        for (i, ds) in mutualDefs.enum do
          for d in ds do
            set { ← get with mutDefIdx := (← get).mutDefIdx.insert d.name i }
            mutualIdxs := mutualIdxs.insert d.name i
        let definitions ← withRecrs mutualIdxs $
          mutualDefs.mapM fun ds => ds.mapM $ toYatimaDef true
        let block : Const := .mutDefBlock definitions
        let blockCid ← constToCid block
        addToStore (blockCid, block)

        let mut ret? : Option (ConstCid × Const) := none

        for definition in definitions.join do
          let idx := match (← get).mutDefIdx.find? definition.name with
            | some i => i
            | none => unreachable!
          let defConst := .definitionProj
            ⟨definition.name, definition.lvls, definition.type, blockCid, idx⟩
          let c ← addToStoreAndCache defConst
          if definition.name == struct.name.toString then ret? := some c

        match ret? with
        | some ret => return ret
        | none => throw s!"Constant for '{struct.name}' wasn't compiled"
    | .ctorInfo struct =>
      let (typeCid, type) ← addFix struct.induct <$> toYatimaExpr struct.type -- TODO
      addToStore (typeCid, type)
      match (← read).constMap.find? struct.induct with
      | some (.inductInfo ind) =>
        let name := struct.name
        let idx ← match ind.all.indexOf? ind.name with
          | some i => pure i
          | none => throw s!"'{ind.name}' not found in '{ind.all}'"
        match ind.ctors.indexOf? name with
        | some cidx =>
          if cidx != struct.cidx then
            throw s!"constructor index mismatch: {cidx} != {struct.cidx}"
          let indInfos ← buildInductiveInfoList ind
          let indBlock : Const := .mutIndBlock indInfos
          let indBlockCid ← constToCid indBlock
          addToStore (indBlockCid, indBlock)
          let const : Const := .constructorProj {
            name  := name
            lvls  := struct.levelParams
            type  := typeCid
            block := indBlockCid
            idx   := idx
            cidx  := struct.cidx }
          addToStoreAndCache const
        | none => throw s!"'{name}' wasn't found as a constructor for the inductive '{ind.name}'"
      | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"
      | none => throw s!"Unknown constant '{struct.induct}'"
    | .recInfo struct =>
      let (typeCid, type) ← toYatimaExpr struct.type
      addToStore (typeCid, type)
      let inductName := struct.getInduct
      match (← read).constMap.find? inductName with
      | some (.inductInfo ind) =>
        let indInfos ← buildInductiveInfoList ind
        let indBlock : Const := .mutIndBlock indInfos
        let indBlockCid ← constToCid indBlock
        addToStore (indBlockCid, indBlock)
        match findRecursorIn struct.name indInfos with
        | some (idx, ridx) =>
          let const : Const := .recursorProj {
            name   := struct.name
            lvls   := struct.levelParams
            type   := typeCid
            block  := indBlockCid
            idx    := idx
            ridx   := ridx }
          addToStoreAndCache const
        | none => throw s!"Recursor '{struct.name}' not found as a recursor of '{inductName}'"
      | some const => throw s!"Invalid constant kind for '{const.name}'. Expected 'inductive' but got '{const.ctorName}'"
      | none => throw s!"Unknown constant '{inductName}'"
    | .inductInfo struct =>
      let indInfos ← buildInductiveInfoList struct
      let indBlock : Const := .mutIndBlock indInfos
      let indBlockCid ← constToCid indBlock
      addToStore (indBlockCid, indBlock)

      let mut ret? : Option (ConstCid × Const) := none

      for (idx, name) in struct.all.enum do
        match (← read).constMap.find? name with
        | some const =>
          let (typeCid, type) ← toYatimaExpr const.type
          addToStore (typeCid, type)
          let const := .inductiveProj {
            name := name
            lvls := const.levelParams
            type := typeCid
            block := indBlockCid
            idx := idx }
          let c ← addToStoreAndCache const
          if name == struct.name then ret? := some c
        | none => throw s!"Unknown constant '{name}'"
      match ret? with
      | some ret => return ret
      | none => throw s!"Constant for '{struct.name}' wasn't compiled"

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
      CompileM $ ConstCid × Const := do
    match (← get).cache.find? const.name with
    | some c => pure c
    | none   => toYatimaConst const

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
      | none, some _ => return .gt
      | some _, none => return .lt
      | none, none => do
        match (← read).constMap.find?' x, (← read).constMap.find?' y with
        | some xConst, some yConst => do
          let xCid := (← processYatimaConst xConst).fst
          let yCid := (← processYatimaConst yConst).fst
          return (compare xCid.anon yCid.anon)
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

  partial def cmpDef (names : Std.RBMap Lean.Name Nat compare)
    (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) :
      CompileM Ordering := do
    let ls := compare x.levelParams.length y.levelParams.length
    let ts ← cmpExpr names x.type y.type
    let vs ← cmpExpr names x.value y.value
    return concatOrds [ls, ts, vs]

  partial def eqDef (names : Std.RBMap Lean.Name Nat compare)
    (x : Lean.DefinitionVal) (y : Lean.DefinitionVal) :
      CompileM Bool := do
    match (← cmpDef names x y) with
      | .eq => pure true
      | _ => pure false

  /-- todo -/
  partial def sortDefs (dss : List (List Lean.DefinitionVal)) :
      CompileM (List (List Lean.DefinitionVal)) := do
    let enum (ll : List (List Lean.DefinitionVal)) :=
      Std.RBMap.ofList (ll.enum.map fun (n, xs) => xs.map (·.name, n)).join
    let names := enum dss
    let newDss ← (← dss.mapM fun ds =>
      match ds with
      | []  => unreachable!
      | [d] => return [[d]]
      | ds  => return (← List.groupByM (eqDef names) $
        ← ds.sortByM (cmpDef names))).joinM

    -- must normalize, see comments
    let normDss := dss.map fun ds => List.sort $ ds.map (·.name)
    let normNewDss := newDss.map fun ds => List.sort $ ds.map (·.name)
    if normDss == normNewDss then
      return newDss
    else
      sortDefs newDss

end

open PrintLean PrintYatima in
def buildStore (constMap : Lean.ConstMap) (log : Bool) : CompileM Store := do
  constMap.forM fun name const => do
    if log then
      dbg_trace "\n========================================="
      dbg_trace s!"Processing: {name}"
      dbg_trace "========================================="
    if log then
      dbg_trace "------------- Lean constant -------------"
      dbg_trace s!"{printLeanConst const}"
    let (_, const) ← processYatimaConst const
    if log then
      dbg_trace "------------ Yatima constant ------------"
      dbg_trace s!"{← printYatimaConst true const}"
  return (← get).store

def extractEnv (map map₀ : Lean.ConstMap) (log : Bool) (stt : CompileState) :
    Except String CompileState :=
  let map  := Lean.filterConstants map
  let map₀ := Lean.filterConstants map₀
  let delta : Lean.ConstMap := map.fold
    (init := Lean.SMap.empty) fun acc n c =>
      match map₀.find? n with
      | some c' => if c == c' then acc else acc.insert n c
      | none    => acc.insert n c
  CompileM.run ⟨map, [], [], .empty⟩ stt (buildStore delta log)

def getPaths : IO Lean.SearchPath := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["print-paths"]
  }
  let split := out.stdout.splitOn "\"oleanPath\":[" |>.getD 1 ""
  let split := split.splitOn "],\"loadDynlibPaths\":[" |>.getD 0 ""
  return split.replace "\"" "" |>.splitOn ","|>.map fun s => ⟨s⟩

def runFrontend (filePath : System.FilePath)
  (log : Bool := false) (stt : CompileState := default) :
    IO $ Except String CompileState := do
  Lean.initSearchPath (← Lean.findSysroot) (← getPaths)
  let (env, ok) ← Lean.Elab.runFrontend (← IO.FS.readFile filePath) .empty
    filePath.toString default
  if ok then
    let importFile := env.header.imports.map (·.module) |>.foldl
      (init := "prelude\n")
      fun acc m => s!"{acc}import {m}\n"
    let (env₀, _) ← Lean.Elab.runFrontend importFile .empty default default
    match extractEnv env.constants env₀.constants log stt with
    | .ok  stt => return .ok stt
    | .error e => return .error e
  else
    return .error s!"Lean frontend failed on file {filePath}"

end Yatima.Compiler
