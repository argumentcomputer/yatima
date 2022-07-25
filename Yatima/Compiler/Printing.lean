import Yatima.Compiler.CompileM

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
    !(Expr.isVarFree name body) && bInfo == .default
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

  partial def printExpr (e : Expr) : CompileM String := match e with
    | .var name _ => return s!"{name}"
    | .sort _ => return "Sort"
    | .const name .. => return s!"{name}"
    | .app func body =>
      return s!"{← printApp func body}"
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

partial def printRecursorRule (b : Bool) : (if b then Constructor else RecursorRule) → CompileM String :=
  match b with
  | .false => fun rule => do
    let ctor := rule.ctor.name
    return s!"{ctor} {rule.fields} {← printExpr rule.rhs}"
  | .true => fun ctor => do
    return s!"{ctor.name} {ctor.fields} {← printExpr ctor.rhs}"

partial def printExtRecursor (cid : String) (recr : ExtRecursor) : CompileM String := do
  let rules ← recr.rules.mapM $ printRecursorRule .false
  return s!"{cid}recursor {recr.name} {recr.lvls} : {← printExpr recr.type}\n" ++
          s!"external\n" ++
          s!"Rules:\n{rules}"

partial def printIntRecursor (cid : String) (recr : IntRecursor) : CompileM String := do
  return s!"{cid}recursor {recr.name} {recr.lvls} : {← printExpr recr.type}\n" ++
          s!"internal\n"

partial def printConstructors (ctors : List Constructor) : CompileM String := do
  let ctors ← ctors.mapM fun ctor => do
    return s!"| {ctor.name} : {← printExpr ctor.type}"
  return "\n".intercalate ctors

partial def printInductive (ind : Inductive) : CompileM String := do
  let indHeader := s!"{printIsSafe ind.safe}inductive {ind.name} {ind.lvls} : {← printExpr ind.type}"
  return s!"{indHeader}\n"

partial def printYatimaConst (const : Const) : CompileM String := do
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
    return s!"{cid}{printIsSafe ctor.safe}constructor {ctor.name} {ctor.lvls} : {← printExpr ctor.type}"
  | .extRecursor recr => do
    printExtRecursor cid recr
  | .intRecursor recr => do
    printIntRecursor cid recr

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
