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
  | some (const, cid) => pure cid
  | none => throw s!"Could not find cid of {name} in context"

def getConst (constCid : ConstCid) : CompileM Const := do
  match (← get).store.const_cache.find? constCid with
  | some const => pure const
  | none => throw "Could not find constant of cid in context"

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

def isAtom : Expr → Bool 
  | .const .. | .var .. | .lit .. | .lty .. => true 
  | _ => false

def isBinder : Expr → Bool 
  | .lam .. | .pi .. => true 
  | _ => false

def isProp (expr : Expr) : CompileM Bool := do
  match expr with
  | .sort cid =>
    match (← get).store.univ_cache.find? cid with 
    | some Univ.zero => return true
    | _ => return false 
  | _ => return false 

def printBinder (name : Name) (bInfo : BinderInfo) (type : String) : String :=
  match bInfo with 
  | .implicit => s!"\{{name} : {type}}"
  | .strictImplicit => s!"⦃{name} : {type}⦄"
  | .instImplicit => s!"[{name} : {type}]"
  | _ => s!"({name} : {type})"

mutual 
  partial def printApp (func : Expr) (arg : Expr) : 
      CompileM (String × List Name) := do 
    match func, arg with 
    | (.app func arg1), arg2 => 
      let (app, bounds) ← printApp func arg1
      let (arg2', bounds') ← printExprAux arg2
      if isAtom arg2 || (← isProp arg2) then 
        return (s!"{app} {arg2'}", bounds ++ bounds')
      else  
        return (s!"{app} ({arg2'})", bounds ++ bounds')
    | func, arg =>
      let (func', bounds) ← printExprAux func 
      let (arg', bounds') ← printExprAux arg
      let func' : CompileM String := do 
        if isAtom func || (← isProp func) then return s!"{func'}"
        else return s!"({func'})"
      let arg' : CompileM String := do 
        if isAtom arg || (← isProp arg) then return s!"{arg'}"
        else return s!"({arg'})"
      return (s!"{← func'} {← arg'}", bounds ++ bounds')

  partial def printExprAux : Expr → CompileM (String × List Name)
    | .var name idx => pure (s!"{name}", [name])
    | .sort _ => pure ("Sort", [])
    | .const name .. => pure (s!"{name}", [])
    | .app func arg => do 
      let (func, bound) ← printExprAux func
      let (arg, bound') ← printExprAux arg
      return (s!"({func} {arg})", bound ++ bound')
    | .lam name bInfo type body => do 
      let isBind := isBinder body
      let (type, bound') ← printExprAux type
      let (body, bound) ← printExprAux body
      let name := 
        if bound.contains name then name 
        else "_"
      let bddVar := printBinder name bInfo type
      if body.startsWith "λ " && isBind then 
        return (s!"λ {bddVar} {body.drop 2}", bound ++ bound')
      else 
        return (s!"λ {bddVar} => {body}", bound ++ bound')
    | .pi name bInfo type body => do
      dbg_trace s! "{bInfo}"
      let isBind := isBinder body
      let (type, bound') ← printExprAux type
      let (body, bound) ← printExprAux body
      let bddVar := if bound.contains name then  
        s!"Π {printBinder name bInfo type},"
      else s!"{type} →"
      if isBind then 
        if body.startsWith "Π " then 
          return (s!"{bddVar.dropRight 1} {body.drop 2}", bound ++ bound') 
        else 
          return (s!"{bddVar} {body}", bound ++ bound')
      else 
        return (s!"{bddVar} {body}", bound ++ bound')
    | .letE name type value body => do 
      let (type, bound) ← printExprAux type
      let (body, bound') ← printExprAux body
      let (value, bound'') ← printExprAux value
      return (s!"let {name} : {type} := {value} in {body}", bound ++ bound' ++ bound'')
    | .lit lit => return match lit with
      | .nat num => (s!"{num}", [])
      | .str str => (str, [])
    | .lty lty => return match lty with 
      | .nat => ("Nat", [])
      | .str => ("String", [])
    | .fix name body => do
      let (body, bound) ← printExprAux body
      return (s!"μ {name} {body}", bound)
    | .proj idx expr => do
      let (expr, bound) ← printExprAux expr
      return (s!"proj {idx} {expr}", bound)

  partial def printExpr (expr : Expr) : CompileM String := do 
    let (expr, _) ← printExprAux expr 
    return expr
end 

mutual

  partial def printRecursorRule (cids? : Bool) (rule : RecursorRule) : CompileM String := do
    let ctor ← sorry
    let rhs ← getExpr rule.rhs ctor.name
    return s!"{← printYatimaConst cids? ctor} {rule.fields} {← printExpr rhs}"

  partial def printRules (cids? : Bool) (rules : List RecursorRule) : CompileM String := do
    let rules ← rules.mapM $ printRecursorRule cids?
    return "\n".intercalate rules

  partial def printRecursor (recr : Recursor) : CompileM String := sorry

  partial def printConstructors (ctors : List Constructor) : CompileM String := do
    let ctors ← ctors.mapM fun ctor => do
      pure s!"| {ctor.name} : {← printExpr (← getExpr ctor.type ctor.name)}"
    return "\n".intercalate ctors

  partial def printInductive (ind : Inductive) : CompileM String := do
    let type ← getExpr ind.type ind.name
    let indHeader := s!"{printIsSafe ind.safe}inductive {ind.name} {ind.lvls} : {← printExpr type}"
    let intRecrs := "\n".intercalate (← ind.intRecrs.mapM printRecursor)
    let extRecrs := "\n".intercalate (← ind.extRecrs.mapM printRecursor)
    return s!"{indHeader}\n{← printConstructors ind.ctors}\nInternal recursors:\n{intRecrs}\nExternal recursors:\n{extRecrs}"

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
    | .definition defn => printDefinition defn
    | .inductiveProj proj => do match ← getConst proj.block with
      | .mutIndBlock inds => match inds.get? proj.idx with
        | some ind => printInductive ind
        | none => throw s!"malformed constructor projection '{proj.name}' idx {proj.idx} ≥ '{inds.length}'"
      | _ => throw s!"malformed constructor projection '{proj.name}': doesn't point to an inductive block"
    | .constructorProj proj => do match ← getConst proj.block with
      | .mutIndBlock inds => match inds.get? proj.idx with
        | some ind => match ind.ctors.get? proj.cidx with
          | some ctor =>
            let type ← getExpr ctor.type ctor.name
            return s!"{printIsSafe ind.safe}constructor {ctor.name} {ind.lvls} : {← printExpr type}"
          | none => throw s!"malformed constructor projection '{proj.name}': cidx {proj.cidx} ≥ '{ind.ctors.length}'"
        | none => throw s!"malformed constructor projection '{proj.name}' idx {proj.idx} ≥ '{inds.length}'"
      | _ => throw s!"malformed constructor projection '{proj.name}': doesn't point to an inductive block"
    | .recursorProj proj => do match ← getConst proj.block with
      | .mutIndBlock inds => match inds.get? proj.idx with
        | some ind =>
          let recrs := if proj.intern then ind.intRecrs else ind.extRecrs
          match recrs.get? proj.ridx with
          | some recr =>
            let type ← getExpr recr.type recr.name
            return s!"{printIsSafe ind.safe}recursor {recr.name} {ind.lvls} : {← printExpr type}"
          | none => throw s!"malformed recursor projection '{proj.name}': ridx {proj.ridx} ≥ '{recrs.length}'"
        | none => throw s!"malformed recursor projection '{proj.name}' idx {proj.idx} ≥ '{inds.length}'"
      | _ => throw s!"malformed recursor projection '{proj.name}': doesn't point to an inductive block"
    | .definitionProj proj =>
      return s!"mutdef {proj.name}@{proj.idx} {← printYatimaConst cids? (← getConst proj.block)}"
    | .mutDefBlock dss => do
      let defStrings ← dss.join.mapM printDefinition
      return s!"mutual\n{"\n".intercalate defStrings}\nend"
    | .mutIndBlock inds => do
      let defStrings ← inds.mapM printInductive
      return s!"mutual\n{"\n".intercalate defStrings}\nend"

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
    s!"  {val.all} {val.numParams} {val.numIndices} {val.numMotives} {val.numMinors} {val.k}\n" ++ 
    s!"Rules:\n" ++ "\n".intercalate (val.rules.map toString)

end Yatima.Compiler.PrintLean
