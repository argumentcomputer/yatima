import Yatima.Typechecker.TypecheckM
import Lean.PrettyPrinter

/-!
# Typechecker printing

This module provides rudimentary printing for universes, expressions, and values used for debugging
the typechecker.
-/

open Lean

open Yatima.Typechecker in
def Yatima.Typechecker.ConstNames.getF 
    (constNames : ConstNames) (f : Lurk.F) : Format := 
  match constNames.find? f with
  | some name => toString name
  | none => toString f

namespace Yatima.IR
open Yatima.Typechecker

private abbrev indentD := Std.Format.indentD

private def join (as : Array α) (f : α → Format) : Format := Id.run do
  if h : 0 < as.size then
    let mut result ← f as[0]
    for a in as[1:] do
      result := f!"{result} {← f a}"
    return result
  else
    return .nil

private def prefixJoin (pre : Format) (as : Array α) (f : α → TypecheckM Format) : TypecheckM Format := do
  let mut result := .nil
  for a in as do
    result := f!"{result}{pre}{← f a}"
  return result

def Expr.isProp : Expr → Bool
  | .sort .zero => true
  | _ => false

def Expr.isAtom : Expr → Bool
  | .const .. | .var .. | .lit .. => true
  | .proj _ e => isAtom e
  | e => isProp e

def Expr.isBinder : Expr → Bool
  | .lam .. | .pi .. => true
  | _ => false

def Expr.isArrow : Expr → Bool
  -- | .pi dom img => !(body.isVarFree name) && bInfo == .default
  | _ => false

namespace PP

instance : ToFormat BinderInfo where format
  | .default        => "default"
  | .implicit       => "implicit"
  | .strictImplicit => "strict"
  | .instImplicit   => "inst"

instance : ToFormat QuotKind where format
  | .type => "Quot"
  | .ctor => "Quot.mk"
  | .lift => "Quot.lift"
  | .ind  => "Quot.ind"

open Std.Format in
mutual
  partial def paren (e : Expr) : TypecheckM Format :=
    if e.isAtom then ppExpr e
    else return f!"({← ppExpr e})"  
      
  partial def ppUniv (u : Univ) : Format :=
    match u with
    | .succ a   => s!"{ppSuccUniv 1 a}"
    | .zero     => "0"
    | .imax a b => s!"(imax {ppUniv a} {ppUniv b})"
    | .max  a b => s!"(max {ppUniv a} {ppUniv b})"
    | .var  i => s!"_#{i}"

  partial def ppSuccUniv (acc : Nat) : Univ → Format
    | .zero => s!"{acc}"
    | .succ u => ppSuccUniv (acc + 1) u
    | u => s!"{acc}+{ppUniv u}"

  partial def ppUnivs (us : List Univ) : Format :=
    bracket "{" (joinSep (us.map ppUniv) ", ") "}"

  partial def ppExpr (e : Expr) : TypecheckM Format := do
    let constNames := (← read).constNames
    match e with
    | .var name us => return f!"v_{name}@{ppUnivs us}"
    | .sort u => return f!"Sort {ppUniv u}"
    | .const name us =>
      return f!"{constNames.getF name}@{ppUnivs us}"
    | .app func body => match func with
      | .app .. => return f!"{← ppExpr func} {← paren body}"
      | _ => return f!"{← paren func} {← paren body}"
    | .lam type body =>
      return f!"fun (_ : {← ppExpr type}) =>{indentD (← ppExpr body)}"
    | .pi dom img =>
      return f!"(_ : {← ppExpr dom}) → {← ppExpr img}"
    | .letE type value body =>
      return f!"let _ : {← ppExpr type} := {← ppExpr value}" 
        ++ ";" ++ .line ++ f!"{← ppExpr body}"
    | .lit lit => match lit with
      | .natVal num => return f!"{num}"
      | .strVal str => return f!"\"{str}\""
    | .proj idx expr => return f!"{← paren expr}.{idx})"
end

partial def ppDefinition (defn : Definition) : TypecheckM Format :=
  let part := if defn.part then "partial " else ""
  return f!"{part}def _ {defn.lvls} : {← ppExpr defn.type} :={indentD (← ppExpr defn.value)}"

partial def ppRecursorRule (rule : RecursorRule) : TypecheckM Format :=
  return f!"fields := {rule.fields}" ++ .line ++ f!"{← ppExpr rule.rhs}"

partial def ppRecursor (recr : Recursor) : TypecheckM Format :=
  let rules := Array.mk recr.rules
  let internal := if recr.internal then "internal" else "external"
  return f!"{internal} recursor _ (lvls := {recr.lvls}) : {← ppExpr recr.type}{indentD (← prefixJoin .line rules ppRecursorRule)}"

partial def ppConstructor (ctor : Constructor) : TypecheckM Format :=
  let fields := f!"idx := {ctor.idx}" ++ .line ++ 
                f!"params := {ctor.params}" ++ .line ++ 
                f!"fields := {ctor.fields}"
  return f!"| _ {ctor.lvls} : {← ppExpr ctor.type}{indentD fields}"

partial def ppConstructors (ctors : List Constructor) : TypecheckM Format :=
  return f!"{← prefixJoin .line (Array.mk ctors) ppConstructor}"

partial def ppInductive (ind : Inductive) : TypecheckM Format := do
  let indHeader := f!"inductive _ {ind.lvls} : {← ppExpr ind.type}" 
  let fields := f!"recr := {ind.recr}" ++ .line ++
                f!"refl := {ind.refl}" ++ .line ++
                f!"unit := {ind.unit}" ++ .line ++
                f!"params := {ind.params}" ++ .line ++
                f!"indices := {ind.indices}" ++ .line ++
                f!"struct := {ind.struct}"
  return f!"{indHeader} with{indentD fields}"

partial def ppConst (const : Const) : TypecheckM Format :=
  match const with
  | .axiom ax => return f!"axiom _ {ax.lvls} : {← ppExpr ax.type}"
  | .theorem thm =>
    return f!"theorem _ {thm.lvls} : {← ppExpr thm.type} :={indentD (← ppExpr thm.value)}"
  | .opaque opaq =>
    return f!"opaque _ {opaq.lvls} {← ppExpr opaq.type} :={indentD (← ppExpr opaq.value)}"
  | .quotient quot =>
    return f!"quot _ {quot.lvls} : {← ppExpr quot.type} :={indentD (format quot.kind)}"
  | .definition defn =>
    ppDefinition defn
  | .inductiveProj ind => return f!"{reprStr ind}"
  | .constructorProj ctor => return f!"{reprStr ctor}"
  | .recursorProj recr => return f!"{reprStr recr}"
  | .definitionProj defn => return f!"{reprStr defn}"
  | .mutDefBlock block => 
    return f!"{← prefixJoin ("\n" ++ .line) (Array.mk block) ppDefinition}"
  | .mutIndBlock block =>
    return f!"{← prefixJoin ("\n" ++ .line) (Array.mk block) ppInductive}"

end Yatima.IR.PP

namespace Yatima.Typechecker

open IR PP Lean Std.Format

private abbrev indentD := Std.Format.indentD

def TypedExpr.isProp : TypedExpr → Bool
  | .sort _ .zero => true
  | _ => false

def TypedExpr.isAtom : TypedExpr → Bool
  | .const .. | .var .. | .lit .. => true
  | .proj _ _ _ e => isAtom e
  | e => isProp e

namespace PP

mutual
  partial def paren (e : TypedExpr) : TypecheckM Format :=
    if e.isAtom then ppTypedExpr e
    else return f!"({← ppTypedExpr e})"

  /-- Printer of expressions -/
  partial def ppTypedExpr : TypedExpr → TypecheckM Format
    | .var _ idx => return f!"v_{idx}"
    | .sort _ u => return f!"Sort {ppUniv u}"
    | .const _ k univs =>
      return f!"{(← read).constNames.getF k}@{ppUnivs univs}"
    | .app _ fnc arg => match fnc with
      | .app .. => return f!"{← ppTypedExpr fnc} {← paren arg}"
      | _ => return f!"{← paren fnc} {← paren arg}"
    | .lam _ dom bod =>
      return f!"fun (_ : {← ppTypedExpr dom}) =>{indentD (← ppTypedExpr bod)}"
    | .pi _ dom cod =>
      return f!"(_: {← ppTypedExpr dom}) → {← ppTypedExpr cod}"
    | .letE _ typ val bod => return f!"let _ : {← ppTypedExpr typ} := {← ppTypedExpr val} in {← ppTypedExpr bod}"
    | .lit _ (.natVal x) => return f!"{x}"
    | .lit _ (.strVal x) => return f!"\"{x}\""
    | .proj _ _ idx val => return f!"{← ppTypedExpr val}.{idx}"

end

mutual
  partial def parenWith (e : TypedExpr) (env : Env) : TypecheckM Format :=
    if e.isAtom then ppTypedExprWith e env
    else return f!"({← ppTypedExprWith e env})"

  /-- Auxiliary function to print the body of a lambda expression given `env : Env` -/
  private partial def ppTypedExprWith (expr : TypedExpr) (env : Env) : TypecheckM Format :=
    match expr with
    | .var _ 0 => return f!"v_0"
    | .var _ (idx + 1) =>
      match env.exprs.get? idx with
     | some val => ppValue val.get
     | none => return f!"!_@{idx}!"
    | .sort _ u => return f!"Sort {ppUniv u}"
    | .const _ k univs => return f!"{(← read).constNames.getF k}@{ppUnivs univs}" 
    | .app _ fnc arg => match fnc with
      | .app .. => return f!"{← ppTypedExprWith fnc env} {← parenWith arg env}"
      | _ => return f!"{← parenWith fnc env} {← parenWith arg env}"
    -- | .app _ fnc arg => f!"({← ppTypedExprWith fnc env} {← ppTypedExprWith arg env})"
    | .lam _ dom bod =>
      return f!"fun (_ : {← ppTypedExprWith dom env}) =>{indentD (← ppTypedExprWith bod env)}"
    | .pi _ dom cod =>
      return f!"(_ : {← ppTypedExprWith dom env}) → {← ppTypedExprWith cod env}"
    | .letE _ typ val bod => return f!"let _ : {← ppTypedExprWith typ env} := {← ppTypedExprWith val env} in {← ppTypedExprWith bod env}"
    | .lit _ (.natVal x) => return f!"{x}"
    | .lit _ (.strVal x) => return f!"\"{x}\""
    | .proj _ _ idx val => return f!"{← ppTypedExprWith val env}.{idx}"

  /-- Auxiliary function to print a chain of unevaluated applications as a single application -/
  private partial def ppSpine (neu : Neutral) (args : Args) : TypecheckM Format := do
    let neu := ← match neu with
      | .fvar idx .. => return f!"fv_{idx}"
      | .const k univs => return f!"{(← read).constNames.getF k}@{ppUnivs univs}"
      | .proj _ idx val => return f!"{← ppValue val.value}.{idx}"
    List.foldrM (fun arg str => return f!"{str} {← ppValue arg.1.get}") neu args

  /-- Printer of typechecker values -/
  partial def ppValue (val : Value) : TypecheckM Format :=
    match val with
    | .sort u => return f!"Sort {ppUniv u}"
    | .app neu args => ppSpine neu args
    | .lam dom bod ctx =>
      return f!"fun (_ : {← ppValue dom.get}) =>{indentD (← ppTypedExprWith bod ctx)}"
    | .pi dom cod ctx =>
      return f!"(_ : {← ppValue dom.get}) → {← ppTypedExprWith cod ctx}"
    | .lit (.natVal x) => return f!"{x}"
    | .lit (.strVal x) => return f!"\"{x}\""
    | .exception e => return f!"exception {e}"
end

-- instance : ToFormat TypedExpr where format := ppTypedExpr
-- instance : ToString TypedExpr where toString := pretty ∘ ppTypedExpr
-- instance : ToFormat Value where format := ppValue
-- instance : ToString Value where toString := pretty ∘ ppValue

def ppTypecheckCtx : TypecheckM Format := do
  let ⟨lvl, env, types, _, _, _, _, _, _⟩ ← read
  let env := ← match env with
    | .mk vals us => do
      let vals : List Value := vals.map fun v => SusValue.get v
      let fields := f!"vals := {← vals.mapM ppValue}" ++ line ++ f!"us := {us.map ppUniv}"
      return f!"env with{indentD fields}"
  let types ← types.mapM fun t => ppValue t.get
  let fields := f!"lvl := {lvl}" ++ line ++ f!"env := {env}" ++ line ++ f!"types := {types}"
  return f!"typecheckCtx with{indentD fields}"

end Yatima.Typechecker.PP
