import Yatima.Compiler.CompileM
import Yatima.Cid

def printIsSafe (x: Bool) : String :=
  if x then "" else "unsafe "

namespace Yatima.Compiler.PrintYatima

open Yatima.Compiler.CompileM

def printDefSafety : Yatima.DefinitionSafety → String
  | .unsafe  => "unsafe "
  | .safe    => ""
  | .partial => "partial "

def getCid (name : Name) : CompileM ConstCid := do
  match (← get).cache.find? name with
  | some (const, cid) => pure cid
  | none => throw s!"Could not find cid of {name} in context"

def getConst (constCid : ConstCid) : CompileM Const := do
  match (← get).store.const_cache.find? constCid with
  | some const => pure const
  | none => throw "Could not find constant of cid in context"

def getCtor (proj : ConstructorProj) : CompileM (Inductive × Constructor) := 
  do match ← getConst proj.block with
  | .mutIndBlock inds => match inds.get? proj.idx with
    | some ind => match ind.ctors.get? proj.cidx with
      | some ctor => return (ind, ctor)
      | none => throw s!"malformed constructor projection '{proj.name}': cidx {proj.cidx} ≥ '{ind.ctors.length}'"
    | none => throw s!"malformed constructor projection '{proj.name}' idx {proj.idx} ≥ '{inds.length}'"
  | _ => throw s!"malformed constructor projection '{proj.name}': doesn't point to an inductive block"  

def getRecr (proj : RecursorProj) : CompileM (Inductive × Recursor) := 
  do match ← getConst proj.block with
  | .mutIndBlock inds => match inds.get? proj.idx with
    | some ind =>
      let recrs := if proj.intern then ind.intRecrs else ind.extRecrs
      match recrs.get? proj.ridx with
      | some recr => return (ind, recr)
      | none => throw s!"malformed recursor projection '{proj.name}': ridx {proj.ridx} ≥ '{recrs.length}'"
    | none => throw s!"malformed recursor projection '{proj.name}' idx {proj.idx} ≥ '{inds.length}'"
  | _ => throw s!"malformed recursor projection '{proj.name}': doesn't point to an inductive block"

def getExpr (exprCid : ExprCid) (name : Name) : CompileM Expr := do
  match (← get).store.expr_cache.find? exprCid with
  | some expr => pure expr
  | none => throw s!"Could not find type of {name} in context"

def printCid (name : Name) : CompileM String := do 
  let cid ← getCid name 
  pure $ s!"anon: {cid.anon.data}\n" ++
         s!"meta: {cid.meta.data}\n"

instance : ToString QuotKind where toString
  | .type => "Quot"
  | .ctor => "Quot.mk"
  | .lift => "Quot.lift"
  | .ind  => "Quot.ind"

instance : ToString Ordering where toString
  | .lt => "lt"
  | .gt => "gt"
  | .eq => "eq"

mutual

  partial def printRecursorRule (ind : Inductive) (rule : RecursorRule) : CompileM String := do
    dbg_trace s!"call rule: uwu"
    let ctor := do match rule.ctor with 
      | .inl idx => 
        match ind.ctors.get? idx with 
        | some ctor => return ctor.name 
        | none => throw s!"out of bounds: wanted constructor {idx + 1} when {ind.name} only has {ind.ctors.length}"
      | .inr cid => return (← getConst cid).name
    let rhs ← getExpr rule.rhs (← ctor)
    return s!"{← ctor} {rule.fields} {← printExpr rhs}"

  partial def printRules (ind : Inductive) (rules : List RecursorRule) : CompileM String := do
    let rules ← rules.mapM $ printRecursorRule ind
    return "\n".intercalate rules

  partial def printConstructors (ctors : List Constructor) : CompileM String := do
    let ctors ← ctors.mapM fun ctor => do
      pure s!"| {ctor.name} : {← printExpr (← getExpr ctor.type ctor.name)}"
    return "\n".intercalate ctors

  partial def printInductive (ind : Inductive) : CompileM String := do
    let type ← getExpr ind.type ind.name
    let indHeader := s!"{printIsSafe ind.safe}inductive {ind.name} {ind.lvls} : {← printExpr type}"
    -- let intRecrs := "\n".intercalate (← ind.intRecrs.mapM printRecursor)
    -- let extRecrs := "\n".intercalate (← ind.extRecrs.mapM printRecursor)
    return s!"{indHeader}\n{← printConstructors ind.ctors}"
      -- \nInternal recursors:\n{intRecrs}\nExternal recursors:\n{extRecrs}

  partial def printExpr : Expr → CompileM String
    | .var name idx => pure s!"{name}.{idx}"
    | .sort _ => pure "Sort"
    | .const name .. => pure s!"{name}"
    | .app func body =>
      return s!"({← printExpr func} {← printExpr body})"
    | .lam name _ type body =>
      return s!"(λ {name} : {← printExpr type}, {← printExpr body})"
    | .pi name _ type body =>
      return s!"(Π {name} : {← printExpr type}, {← printExpr body})"
    | .letE name type value body =>
      return s!"(let {name} : {← printExpr type} := {← printExpr value} in {← printExpr body})" 
    | .lit lit => return match lit with
      | .nat num => s!"{num}"
      | .str str => str
    | .lty lty => return match lty with 
      | .nat => "Nat"
      | .str => "String"
    | .fix name body => return s!"(μ {name} {← printExpr body})"
    | .proj idx expr => return s!"(proj {idx} {← printExpr expr})"

  partial def printDefinition (defn : Definition) : CompileM String := do
    let type ← getExpr defn.type defn.name
    let value ← getExpr defn.value defn.name
    return s!"{printDefSafety defn.safety}def {defn.name} {defn.lvls} : {← printExpr type} :=\n" ++
           s!"  {← printExpr value}"

  partial def printYatimaConst (cids? : Bool) (const : Const) : CompileM String := do
    let cid := 
      if cids? then ← printCid const.name 
      else ""
    match const with 
    | .axiom ax => do
      let type ← getExpr ax.type ax.name
      return s!"{cid}{printIsSafe ax.safe}axiom {ax.name} {ax.lvls} : {← printExpr type}"
    | .theorem thm => do
      let type ← getExpr thm.type thm.name
      let value ← getExpr thm.value thm.name
      return s!"{cid}theorem {thm.name} {thm.lvls} : {← printExpr type} :=\n" ++
             s!"  {← printExpr value}" 
    | .opaque opaq => do
      let type ← getExpr opaq.type opaq.name
      let value ← getExpr opaq.value opaq.name
      return s!"{cid}{printIsSafe opaq.safe}opaque {opaq.name} {opaq.lvls} {← printExpr type} :=\n" ++
             s!"  {← printExpr value}"
    | .quotient quot => do
      let type ← getExpr quot.type quot.name
      return s!"{cid}quot {quot.name} {quot.lvls} : {← printExpr type} :=\n" ++
             s!"  {quot.kind}"
    | .definition defn => return s!"{cid}{← printDefinition defn}"
    | .inductiveProj proj => do match ← getConst proj.block with
      | .mutIndBlock inds => match inds.get? proj.idx with
        | some ind => return s!"{cid}{← printInductive ind}"
        | none => throw s!"malformed constructor projection '{proj.name}' idx {proj.idx} ≥ '{inds.length}'"
      | _ => throw s!"malformed constructor projection '{proj.name}': doesn't point to an inductive block"
    | .constructorProj proj => do 
      let (ind, ctor) ← getCtor proj 
      let type ← getExpr ctor.type ctor.name
      return s!"{cid}{printIsSafe ind.safe}constructor {ctor.name} {ind.lvls} : {← printExpr type}"
    | .recursorProj proj => do 
      let (ind, recr) ← getRecr proj 
      let type ← getExpr recr.type recr.name
      let intern := if proj.intern then "internal" else "external"
      return s!"{cid}{printIsSafe ind.safe}recursor {recr.name} {ind.lvls} : {← printExpr type}\n" ++ 
             s!"{intern}\n" ++ 
             s!"Rules:\n{← printRules ind recr.rules}"
    | .definitionProj proj =>
      return s!"mutdef {proj.name}@{proj.idx} {← printYatimaConst cids? (← getConst proj.block)}"
    | .mutDefBlock dss => do
      let defStrings ← dss.join.mapM printDefinition
      return s!"{cid}mutual\n{"\n".intercalate defStrings}\nend"
    | .mutIndBlock inds => do
      let defStrings ← inds.mapM printInductive
      return s!"{cid}mutual\n{"\n".intercalate defStrings}\nend"

end

end Yatima.Compiler.PrintYatima

namespace Yatima.Compiler.PrintLean

open Lean

instance : ToString Lean.RecursorRule where
  toString x := s!"{x.ctor} {x.nfields} {x.rhs}"

def printDefSafety : Lean.DefinitionSafety -> String
  | .unsafe  => "unsafe "
  | .safe    => ""
  | .partial => "partial "

instance : ToString Lean.QuotKind where toString
  | .type => "Quot"
  | .ctor => "Quot.mk"
  | .lift => "Quot.lift"
  | .ind  => "Quot.ind"

def printLeanConst : Lean.ConstantInfo -> String
  | .axiomInfo  val =>
    s!"{printIsSafe !val.isUnsafe}axiom {val.name} {val.levelParams} : {val.type}"
  | .defnInfo   val =>
    s!"{printDefSafety val.safety}def {val.name} {val.levelParams} : {val.type} :=\n  {val.value}"
  | .thmInfo    val =>
    s!"theorem {val.name} {val.levelParams} : {val.type} :=\n  {val.value}"
  | .opaqueInfo val =>
    s!"{printIsSafe !val.isUnsafe}opaque {val.name} {val.levelParams} {val.type} :=\n  {val.value}"
  | .quotInfo   val =>
    s!"quot {val.name} {val.levelParams} : {val.type} :=\n  {val.kind}"
  | .inductInfo val =>
    s!"{printIsSafe !val.isUnsafe}inductive {val.name} {val.levelParams} : {val.type} :=\n" ++
    s!"  {val.numParams} {val.numIndices} {val.all} {val.ctors} {val.isRec} {val.isUnsafe} {val.isReflexive} {val.isNested}"
  | .ctorInfo   val =>
    s!"{printIsSafe !val.isUnsafe}constructor {val.name} {val.levelParams} : {val.type} :=\n" ++
    s!"  {val.induct} {val.cidx} {val.numParams} {val.numFields}"
  | .recInfo    val =>
    s!"{printIsSafe !val.isUnsafe}recursor {val.name} {val.levelParams} : {val.type} :=\n" ++
    s!"  {val.all} {val.numParams} {val.numIndices} {val.numMotives} {val.numMinors} {val.rules} {val.k}"

end Yatima.Compiler.PrintLean
