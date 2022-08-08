import Yatima.Compiler.CompileM

def printIsSafe (x: Bool) : String :=
  if x then "" else "unsafe "

def rulesSep : String :=
  "\n------------------\n"

namespace Yatima.Compiler.PrintYatima

abbrev PrintM := ReaderT CompileState $ ExceptT CompileError Id

open Yatima.Compiler.CompileM

instance : ToString BinderInfo where toString
  | .default        => "default"
  | .implicit       => "implicit"
  | .strictImplicit => "strict"
  | .instImplicit   => "inst"
  | .auxDecl        => "auxDecl"

def printDefSafety : Yatima.DefinitionSafety → String
  | .unsafe  => "unsafe "
  | .safe    => ""
  | .partial => "partial "

def getCid (name : Name) : PrintM ConstCid := do
  match (← read).cache.find? name with
  | some (cid, _) => return cid
  | none => throw $ .notFoundInCache name

def printCid (name : Name) : PrintM String := do
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

def isProp : Expr → Bool
  | .sort Univ.zero => true
  | _ => false

def isAtomAux : Expr → Bool
  | .const .. | .var .. | .lit .. | .lty .. => true
  | _ => false

def isAtom : Expr → Bool
  | .const .. | .var .. | .lit .. | .lty .. => true
  | .proj _ e => isAtom e
  | e => isProp e

def isBinder : Expr → Bool
  | .lam .. | .pi .. => true
  | _ => false

def isArrow : Expr → Bool
  | .pi name bInfo _ body =>
    !(Expr.isVarFree name body) && bInfo == .default
  | _ => false

def printBinder (name : Name) (bInfo : BinderInfo) (type : String) : String :=
  match bInfo with
  | .implicit => s!"\{{name} : {type}}"
  | .strictImplicit => s!"⦃{name} : {type}⦄"
  | .instImplicit => s!"[{name} : {type}]"
  | _ => s!"({name} : {type})"

mutual
  partial def printBinding (isPi : Bool) (e : Expr) : PrintM String := do
    match e, isArrow e, isPi with
    | .pi name bInfo type body, false, true
    | .lam name bInfo type body, _, false =>
      return s!" {printBinder name bInfo (← printExpr type)}" ++
             (← printBinding isPi body)
    | _, _, _ =>
      let sep := if isPi then ", " else " => "
      return sep ++ (← printExpr e)

  partial def paren (e : Expr) : PrintM String := do
    if isAtom e then printExpr e
    else return s!"({← printExpr e})"

  partial def printUniv (u : Univ) : PrintM String := do match u with
    | .zero       => pure "0"
    | .succ v     => pure s!"(succ {← printUniv v})"
    | .max  v w   => pure s!"(max {← printUniv v} {← printUniv w})"
    | .imax v w   => pure s!"(imax {← printUniv v} {← printUniv w})"
    | .var  n idx => pure s!"({n}.{idx})"

  partial def printExpr (e : Expr) : PrintM String := match e with
    | .var name _ => return s!"{name}"
    | .sort u => return s!"Sort {← printUniv u}"
    | .const name .. => return s!"{name}"
    | .app func body => match func with
      | .app .. => return s!"{← printExpr func} {← paren body}"
      | _ => return s!"{← paren func} {← paren body}"
    | .lam name bInfo type body =>
      return s!"λ{← printBinding false (.lam name bInfo type body)}"
    | .pi name bInfo type body => do
      let arrow := isArrow e || (bInfo == .default && name == "")
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
    | .proj idx expr => return s!"{← paren expr}.{idx})"
end

partial def printRecursorRule (rule : RecursorRule) : PrintM String := do
  let ctor := rule.ctor.name
  return s!"{ctor} {rule.fields} {← printExpr rule.rhs}"

partial def printExtRecursor (cid : String) (recr : ExtRecursor) : PrintM String := do
  let rules ← recr.rules.mapM printRecursorRule
  return s!"{cid}recursor {recr.name} {recr.lvls} : {← printExpr recr.type}\n" ++
          s!"\nExternal rules:{rulesSep}{rulesSep.intercalate rules}"

partial def printIntRecursor (cid : String) (recr : IntRecursor) : PrintM String := do
  return s!"{cid}recursor {recr.name} {recr.lvls} : {← printExpr recr.type}\n" ++
          s!"internal\n"

partial def printConstructors (ctors : List Constructor) : PrintM String := do
  let ctors ← ctors.mapM fun ctor => do
    return s!"| {printIsSafe ctor.safe}{ctor.name} {ctor.lvls} : {← printExpr ctor.type} [fields : (idx := {ctor.idx}) (params := {ctor.params}) (fields := {ctor.fields}) (rhs := {← printExpr ctor.rhs})]"
  return "\n".intercalate ctors

partial def printInductive (ind : Inductive) : PrintM String := do
  let structStr ← match ind.struct with
  | some ctor => printConstructors [ctor]
  | none => pure "none"
  let indHeader := s!"{printIsSafe ind.safe}inductive {ind.name} {ind.lvls} : {← printExpr ind.type} [fields : (recr := {ind.recr}) (refl := {ind.refl}) (unit := {ind.unit}) (params := {ind.params}) (indices := {ind.indices}) (struct := {structStr})]"
  return s!"{indHeader}\n"

partial def printConst (const : Const) : PrintM String := do
  let cid ← printCid const.name
  match const with
  | .axiom ax => do
    return s!"{cid}{printIsSafe ax.safe}axiom {ax.name} {ax.lvls} : {← printExpr ax.type}"
  | .theorem thm => do
    return s!"{cid}theorem {thm.name} {thm.lvls} : {← printExpr thm.type} :=\n" ++
            s!"  {← printExpr thm.value}"
  | .opaque opaq => do
    return s!"{cid}{printIsSafe opaq.safe}opaque {opaq.name} {opaq.lvls} {← printExpr opaq.type} :=\n" ++
            s!"  {← printExpr opaq.value}"
  | .quotient quot => do
    return s!"{cid}quot {quot.name} {quot.lvls} : {← printExpr quot.type} :=\n" ++
            s!"  {quot.kind}"
  | .definition defn => 
    return s!"{printDefSafety defn.safety}def {defn.name} {defn.lvls} : {← printExpr defn.type} :=\n" ++
            s!"  {← printExpr defn.value}"
  | .inductive ind => return s!"{← printInductive ind}"
  | .constructor ctor => do
    return s!"{cid}{printIsSafe ctor.safe}constructor {ctor.name} {ctor.lvls} : {← printExpr ctor.type}\n| internal rule: {← printExpr ctor.rhs}"
  | .extRecursor recr => printExtRecursor cid recr
  | .intRecursor recr => printIntRecursor cid recr

def printYatimaConst (const : Const) : CompileM String := do
  match ReaderT.run (printConst const) (← get) with
  | .ok    s => pure s
  | .error e => throw e

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
    s!"\nRules:{rulesSep}{rulesSep.intercalate (val.rules.map toString)}"

end Yatima.Compiler.PrintLean
