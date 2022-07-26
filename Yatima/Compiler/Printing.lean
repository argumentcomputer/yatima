import Yatima.Compiler.CompileM
import Yatima.Cid

def printIsSafe (x: Bool) : String :=
  if x then "" else "unsafe "

namespace Yatima.Compiler.PrintYatima

open Yatima.Compiler.CompileM

instance : ToString BinderInfo where
  toString bInfo := match bInfo with
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strict"
  | .instImplicit => "inst"
  | .auxDecl => "auxDecl"

def printDefSafety : Yatima.DefinitionSafety → String
  | .unsafe  => "unsafe "
  | .safe    => ""
  | .partial => "partial "

def getCid (name : Name) : CompileM ConstCid := do
  match (← get).cache.find? name with
  | some (cid, _) => pure cid
  | none => throw s!"Could not find cid of {name} in context"

def getConst (constCid : ConstCid) : CompileM Const := do
  match (← get).store.const_cache.find? constCid with
  | some const => return const
  | none => throw "Could not find constant of cid in context"

def getCtor (proj : ConstructorProj) : CompileM (Inductive × Constructor) :=
  do match ← getConst proj.block with
  | .mutIndBlock inds => match inds.get? proj.idx with
    | some ind => match ind.ctors.get? proj.cidx with
      | some ctor => return (ind, ctor)
      | none => throw s!"malformed constructor projection '{proj.name}': cidx {proj.cidx} ≥ '{ind.ctors.length}'"
    | none => throw s!"malformed constructor projection '{proj.name}' idx {proj.idx} ≥ '{inds.length}'"
  | _ => throw s!"malformed constructor projection '{proj.name}': doesn't point to an inductive block"

def getRecr (proj : RecursorProj) : CompileM (Inductive × (Sigma Recursor)) :=
  do match ← getConst proj.block with
  | .mutIndBlock inds => match inds.get? proj.idx with
    | some ind =>
      match ind.recrs.get? proj.ridx with
      | some recr => return (ind, recr)
      | none => throw s!"malformed recursor projection '{proj.name}': ridx {proj.ridx} ≥ '{ind.recrs.length}'"
    | none => throw s!"malformed recursor projection '{proj.name}' idx {proj.idx} ≥ '{inds.length}'"
  | _ => throw s!"malformed recursor projection '{proj.name}': doesn't point to an inductive block"

def getExpr (exprCid : ExprCid) (name : Name) : CompileM Expr := do
  match (← get).store.expr_cache.find? exprCid with
  | some expr => return expr
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

def isProp (expr : Expr) : CompileM Bool := do
  match expr with
  | .sort Univ.zero => return true
  | _ => return false

def isAtomAux : Expr → Bool
  | .const .. | .var .. | .lit .. | .lty .. => true
  | _ => false

def isAtom : Expr → CompileM Bool
  | .const .. | .var .. | .lit .. | .lty .. => return true
  | .proj _ e => isAtom e
  | e => isProp e

def isBinder : Expr → Bool
  | .lam .. | .pi .. => true
  | _ => false

def isArrow : Expr → Bool
  | .pi name bInfo _ body =>
    !(body.getBVars.contains name) && bInfo == .default
  | _ => false

def printBinder (name : Name) (bInfo : BinderInfo) (type : String) : String :=
  match bInfo with
  | .implicit => s!"\{{name} : {type}}"
  | .strictImplicit => s!"⦃{name} : {type}⦄"
  | .instImplicit => s!"[{name} : {type}]"
  | _ => s!"({name} : {type})"

mutual
  partial def printApp (f : Expr) (arg : Expr) : CompileM String := do
    match f with
    | .app .. => return s!"{← printExpr f} {← paren arg}"
    | _ => return s!"{← paren f} {← paren arg}"

  partial def printBinding (isPi : Bool) (e : Expr) : CompileM String := do
    match e, isArrow e, isPi with
    | .pi name bInfo type body, false, true
    | .lam name bInfo type body, _, false =>
      return s!" {printBinder name bInfo (← printExpr type)}" ++
             (← printBinding isPi body)
    | _, _, _ =>
      let sep := if isPi then ", " else " => "
      return sep ++ (← printExpr e)

  partial def paren (e : Expr) : CompileM String := do
    if (← isAtom e) then printExpr e
    else return s!"({← printExpr e})"

  partial def printExpr : Expr → CompileM String
    | .var name i => return s!"{name}.{i}"
    | .sort _ => return "Sort"
    | .const name .. => return s!"{name}"
    | .app func body =>
      return s!"{← printApp func body}"
    | .lam name bInfo type body =>
      return s!"λ{← printBinding false (.lam name bInfo type body)}"
    | .pi name bInfo type body => do
      let arrow := (!body.getBVars.contains name || name == "") && bInfo == .default
      if !arrow then
        return s!"Π{← printBinding true (.pi name bInfo type body)}"
      else
        return s!"{← paren type} -> " ++
          if isArrow body then ← printExpr body else ← paren body
    | .letE name type value body =>
      return s!"let {name} : {← printExpr type} := {← printExpr value} in {← printExpr body}"
    | .lit lit => return match lit with
      | .nat num => s!"{num}"
      | .str str => s!"\"{str}\""
    | .lty lty => return match lty with
      | .nat => "Nat"
      | .str => "String"
    | .fix name body => return s!"(μ {name} {← printExpr body})"
    | .proj idx expr => return s!"{← paren expr}.{idx})"
end

partial def printRecursorRule (b : Bool) : (if b then Constructor else RecursorRule) → CompileM String :=
  match b with
  | .false => fun rule => do
    let ctor := (← getConst rule.ctor).name
    let rhs ← getExpr rule.rhs ctor
    return s!"{ctor} {rule.fields} {← printExpr rhs}"
  | .true => fun ctor => do
    let rhs ← getExpr ctor.rhs ctor.name
    return s!"{ctor.name} {ctor.fields} {← printExpr rhs}"

partial def printRecursor (cid : String) (ind : Inductive) (b : RecType) : Recursor b → CompileM String :=
  match b with
  | .Extr => fun recr => do
    let type ← getExpr recr.type recr.name
    let rules ← recr.rules.proj₂.mapM $ printRecursorRule .false
    return s!"{cid}{printIsSafe ind.safe}recursor {recr.name} {ind.lvls} : {← printExpr type}\n" ++
            s!"external\n" ++
            s!"Rules:\n{rules}"
  | .Intr => fun recr => do
    let type ← getExpr recr.type recr.name
    let rules ← ind.ctors.mapM $ printRecursorRule .true
    return s!"{cid}{printIsSafe ind.safe}recursor {recr.name} {ind.lvls} : {← printExpr type}\n" ++
            s!"internal\n" ++
            s!"Rules:\n{rules}"

partial def printConstructors (ctors : List Constructor) : CompileM String := do
  let ctors ← ctors.mapM fun ctor => do
    return s!"| {ctor.name} : {← printExpr (← getExpr ctor.type ctor.name)}"
  return "\n".intercalate ctors

partial def printInductive (ind : Inductive) : CompileM String := do
  let type ← getExpr ind.type ind.name
  let indHeader := s!"{printIsSafe ind.safe}inductive {ind.name} {ind.lvls} : {← printExpr type}"
  return s!"{indHeader}\n{← printConstructors ind.ctors}"

partial def printDefinition (defn : Definition) : CompileM String := do
  let type ← getExpr defn.type defn.name
  let value ← getExpr defn.value defn.name
  return s!"{printDefSafety defn.safety}def {defn.name} {defn.lvls} : {← printExpr type} :=\n" ++
          s!"  {← printExpr value}"

partial def printYatimaConst (const : Const) : CompileM String := do
  let cid ← printCid const.name
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
    printRecursor cid ind recr.fst recr.snd
  | .definitionProj proj => do match ← getConst proj.block with
    | .mutDefBlock defs => match defs.get? proj.idx with
      | some ds => match ds.find? (fun d => d.name == proj.name) with
        | some d => return s!"{cid}{← printDefinition d}"
        | none => throw s!"malformed definition projection '{proj.name}' not in weakly equal block '{proj.idx}'"
      | none => throw s!"malformed definition projection '{proj.name}' idx {proj.idx} ≥ '{defs.length}'"
    | _ => throw s!"malformed definition projection '{proj.name}': doesn't point to an definition block"
  -- these two will never happen
  | .mutDefBlock _ => do
    throw s!"Unreachable call to print mutual pointer was reached"
    -- let defStrings ← dss.join.mapM printDefinition
    -- return s!"{cid}mutual\n{"\n".intercalate defStrings}\nend"
  | .mutIndBlock _ => do
    throw s!"Unreachable call to print mutual pointer was reached"
    -- let defStrings ← inds.mapM printInductive
    -- return s!"{cid}mutual\n{"\n".intercalate defStrings}\nend"

end Yatima.Compiler.PrintYatima

namespace Yatima.Compiler.PrintLean

open Lean

instance : ToString Lean.RecursorRule where
  toString x := s!"{x.ctor} {x.nfields} {x.rhs}"

def printDefSafety : Lean.DefinitionSafety → String
  | .unsafe  => "unsafe "
  | .safe    => ""
  | .partial => "partial "

instance : ToString Lean.QuotKind where toString
  | .type => "Quot"
  | .ctor => "Quot.mk"
  | .lift => "Quot.lift"
  | .ind  => "Quot.ind"

def printLeanConst : Lean.ConstantInfo → String
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
    s!"  {val.all} {val.numParams} {val.numIndices} {val.numMotives} {val.numMinors} {val.k}\n" ++
    s!"Rules:\n" ++ "\n".intercalate (val.rules.map toString)

end Yatima.Compiler.PrintLean
