import Lean.PrettyPrinter
import Yatima.Datatypes.Const

open Lean

namespace Yatima.TC

private abbrev indentD := Std.Format.indentD

private def join (as : Array α) (f : α → Format) : Format := Id.run do
  if h : 0 < as.size then
    let mut result ← f as[0]
    for a in as[1:] do
      result := f!"{result} {← f a}"
    return result
  else
    return .nil

private def prefixJoin (pre : Format) (as : Array α) (f : α → Format) : Format := Id.run do
  let mut result := .nil
  for a in as do
    result := f!"{result}{pre}{f a}"
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

instance : ToFormat DefinitionSafety where format
  | .unsafe  => "unsafe "
  | .safe    => ""
  | .partial => "partial "

instance : ToFormat QuotKind where format
  | .type => "Quot"
  | .ctor => "Quot.mk"
  | .lift => "Quot.lift"
  | .ind  => "Quot.ind"

open Std.Format in
mutual
  partial def paren (e : Expr) : Format :=
    if e.isAtom then ppExpr e
    else f!"({ppExpr e})"  
      
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

  partial def ppExpr (e : Expr) : Format := match e with
    | .var name us => 
      let us := bracket "{" (joinSep (us.map ppUniv) ", ") "}"
      f!"v_{name}@{us}"
    | .sort u => f!"Sort {ppUniv u}"
    | .const name us =>
      let us := bracket "{" (joinSep (us.map ppUniv) ", ") "}"
      f!"{name}@{us}"
    | .app func body => match func with
      | .app .. => f!"{ppExpr func} {paren body}"
      | _ => f!"{paren func} {paren body}"
    | .lam type body =>
      f!"fun (_ : {ppExpr type}) =>{indentD (ppExpr body)}"
    | .pi dom img =>
      f!"(_ : {ppExpr dom}) → {ppExpr img}"
    | .letE type value body =>
      f!"let _ : {ppExpr type} := {ppExpr value}" 
        ++ ";" ++ .line ++ f!"{ppExpr body}"
    | .lit lit => match lit with
      | .natVal num => f!"{num}"
      | .strVal str => f!"\"{str}\""
    | .proj idx expr => f!"{paren expr}.{idx})"
end

partial def ppDefinition (defn : Definition) : Format :=
  f!"{format defn.safety}def _ {defn.lvls} : {ppExpr defn.type} :={indentD (ppExpr defn.value)}"

partial def ppRecursorRule (rule : RecursorRule) : Format :=
  f!"fields := {rule.fields}" ++ .line ++ f!"{ppExpr rule.rhs}"

partial def ppRecursor (recr : Recursor) : Format :=
  let rules := Array.mk recr.rules
  let internal := if recr.internal then "internal" else "external"
  f!"{internal} recursor _ (lvls := {recr.lvls}) : {ppExpr recr.type}{indentD (prefixJoin .line rules ppRecursorRule)}"

partial def ppConstructor (ctor : Constructor) : Format :=
  let safe := if ctor.safe then "" else "unsafe "
  let fields := f!"idx := {ctor.idx}" ++ .line ++ 
                f!"params := {ctor.params}" ++ .line ++ 
                f!"fields := {ctor.fields}"
  f!"| {safe}_ {ctor.lvls} : {ppExpr ctor.type}{indentD fields}"

partial def ppConstructors (ctors : List Constructor) : Format :=
  f!"{prefixJoin .line (Array.mk ctors) ppConstructor}"

partial def ppInductive (ind : Inductive) : Format :=
  let safe := if ind.safe then "" else "unsafe "
  let indHeader := f!"{safe}inductive _ {ind.lvls} : {ppExpr ind.type}" 
  let fields := f!"recr := {ind.recr}" ++ .line ++
                f!"refl := {ind.refl}" ++ .line ++
                f!"unit := {ind.unit}" ++ .line ++
                f!"params := {ind.params}" ++ .line ++
                f!"indices := {ind.indices}" ++ .line ++
                f!"struct := {ind.struct}"
  f!"{indHeader} with{indentD fields}"

partial def ppConst (const : Const) : Format :=
  match const with
  | .axiom ax =>
    let safe := if ax.safe then "" else "unsafe "
    f!"{safe}axiom _ {ax.lvls} : {ppExpr ax.type}"
  | .theorem thm =>
    f!"theorem _ {thm.lvls} : {ppExpr thm.type} :={indentD (ppExpr thm.value)}"
  | .opaque opaq =>
    let safe := if opaq.safe then "" else "unsafe "
    f!"{safe}opaque _ {opaq.lvls} {ppExpr opaq.type} :={indentD (ppExpr opaq.value)}"
  | .quotient quot =>
    f!"quot _ {quot.lvls} : {ppExpr quot.type} :={indentD (format quot.kind)}"
  | .definition defn =>
    ppDefinition defn
  | .inductiveProj ind => f!"{reprStr ind}"
  | .constructorProj ctor => f!"{reprStr ctor}"
  | .recursorProj recr => f!"{reprStr recr}"
  | .definitionProj defn => f!"{reprStr defn}"
  | .mutDefBlock block => 
    f!"{prefixJoin ("\n" ++ .line) (Array.mk block) ppDefinition}"
  | .mutIndBlock block =>
    f!"{prefixJoin ("\n" ++ .line) (Array.mk block) ppInductive}"