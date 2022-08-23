import Yatima.Typechecker.Datatypes

namespace Yatima.Typechecker

def printUniv : Univ → String
  | .succ (.zero) => s!"1"
  | .succ a   => s!"1+{printUniv a}"
  | .zero     => "0"
  | .imax a b => s!"(imax {printUniv a} {printUniv b})"
  | .max  a b => s!"(max {printUniv a} {printUniv b})"
  | .var  n i => s!"({n}@{i})"

def printExpr : Expr → String
  | .var nam idx => s!"{nam}^{idx}"
  | .sort u => s!"(Sort {printUniv u})"
  | .const nam k univs => s!"{nam}@{k}.{univs.map printUniv}"
  | .app fnc arg => s!"({printExpr fnc} {printExpr arg})"
  | .lam nam binfo dom bod =>
    match binfo with
    | .implicit => s!"(λ\{{nam}: {printExpr dom}}. {printExpr bod})"
    | .strictImplicit => s!"(λ⦃{nam}: {printExpr dom}⦄. {printExpr bod})"
    | .instImplicit => s!"(λ[{nam}: {printExpr dom}]. {printExpr bod})"
    | _ => s!"(λ({nam}: {printExpr dom}). {printExpr bod})"
  | .pi nam binfo dom cod =>
    match binfo with
    | .implicit => s!"(\{{nam}: {printExpr dom}} → {printExpr cod})"
    | .strictImplicit => s!"(⦃{nam}: {printExpr dom}⦄ → {printExpr cod})"
    | .instImplicit => s!"([{nam}: {printExpr dom}] → {printExpr cod})"
    | _ => s!"(({nam}: {printExpr dom}) → {printExpr cod})"
  | .letE nam typ val bod => s!"let {nam} : {printExpr typ} := {printExpr val} in {printExpr bod}"
  | .lit (.num x) => s!"{x}"
  | .lit (.word x) => s!"\"{x}\""
  | .lty .num => "Number"
  | .lty .word => "Word"
  | .proj idx val => s!"{printExpr val}.{idx}"

mutual

partial def printVal : Value → String
  | .sort u => s!"(Sort {printUniv u})"
  | .app neu args => printSpine neu args
  | .lam nam binfo bod ctx =>
    match binfo with
    | .implicit => s!"(λ\{{nam}}}. {printLamBod bod ctx})"
    | .strictImplicit => s!"(λ⦃{nam}⦄. {printLamBod bod ctx})"
    | .instImplicit => s!"(λ[{nam}]. {printLamBod bod ctx})"
    | _ => s!"(λ({nam}). {printLamBod bod ctx})"
  | .pi nam binfo dom cod ctx =>
    let dom := dom.repr
    match binfo with
    | .implicit => s!"(\{{nam}: {dom}} → {printLamBod cod ctx})"
    | .strictImplicit => s!"(⦃{nam}: {dom}⦄ → {printLamBod cod ctx})"
    | .instImplicit => s!"([{nam}: {dom}] → {printLamBod cod ctx})"
    | _ => s!"(({nam}: {dom}) → {printLamBod cod ctx})"
  | .lit (.num x) => s!"{x}"
  | .lit (.word x) => s!"\"{x}\""
  | .lty .num => "Number"
  | .lty .word => "Word"
  | .proj idx neu args => s!"{printSpine neu args}.{idx}"
  | .exception e => s!"exception {e}"

partial def printLamBod (expr : Expr) (ctx : Context) : String :=
  match expr with
  | .var nam 0 => s!"{nam}^0"
  | .var nam idx =>
    match ctx.exprs.get? (idx-1) with
   | some val => val.repr
   | none => s!"!{nam}^{idx}!"
  | .sort u => s!"(Sort {printUniv u})"
  | .const nam k univs => s!"{nam}@{k}.{univs.map printUniv}"
  | .app fnc arg => s!"({printLamBod fnc ctx} {printLamBod arg ctx})"
  | .lam nam binfo dom bod =>
    match binfo with
    | .implicit => s!"(λ\{{nam}: {printLamBod dom ctx}}. {printLamBod bod ctx})"
    | .strictImplicit => s!"(λ⦃{nam}: {printLamBod dom ctx}⦄. {printLamBod bod ctx})"
    | .instImplicit => s!"(λ[{nam}: {printLamBod dom ctx}]. {printLamBod bod ctx})"
    | _ => s!"(λ({nam}: {printLamBod dom ctx}). {printLamBod bod ctx})"
  | .pi nam binfo dom cod =>
    match binfo with
    | .implicit => s!"(\{{nam}: {printLamBod dom ctx}} → {printLamBod cod ctx})"
    | .strictImplicit => s!"(⦃{nam}: {printLamBod dom ctx}⦄ → {printLamBod cod ctx})"
    | .instImplicit => s!"([{nam}: {printLamBod dom ctx}] → {printLamBod cod ctx})"
    | _ => s!"(({nam}: {printLamBod dom ctx}) → {printLamBod cod ctx})"
  | .letE nam typ val bod => s!"let {nam} : {printLamBod typ ctx} := {printLamBod val ctx} in {printLamBod bod ctx}"
  | .lit (.num x) => s!"{x}"
  | .lit (.word x) => s!"\"{x}\""
  | .lty .num => "Number"
  | .lty .word => "Word"
  | .proj idx val => s!"{printLamBod val ctx}.{idx}"

partial def printSpine (neu : Neutral) (args : Args) : String :=
  match neu with
  | .fvar nam idx .. => List.foldl (fun str arg => s!"({str} {arg.repr})") s!"{nam}#{idx}" args
  | .const nam k univs => List.foldl (fun str arg => s!"({str} {arg.repr})") s!"{nam}@{k}.{univs.map printUniv}" args

end

instance : ToString Expr  where toString := printExpr
instance : ToString Univ  where toString := printUniv
instance : ToString Value where toString := printVal

end Yatima.Typechecker
