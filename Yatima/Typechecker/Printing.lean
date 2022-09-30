import Yatima.Typechecker.Datatypes

/-!
# Typechecker printing

This module provides rudimentary printing for universes, expressions, and values used for debugging
the typechecker.
-/

namespace Yatima.Typechecker

mutual
  /-- Printer of universe levels -/
  def printUniv (u : Univ) : String :=
    match u with
    | .succ a   => s!"{printSuccUniv 1 a}"
    | .zero     => "0"
    | .imax a b => s!"(imax {printUniv a} {printUniv b})"
    | .max  a b => s!"(max {printUniv a} {printUniv b})"
    | .var  n i => s!"({n}#{i})"

  def printSuccUniv (acc : Nat) : Univ → String
    | .zero => s!"{acc}"
    | .succ u => printSuccUniv (acc + 1) u
    | u => s!"{acc}+{printUniv u}"

end

/-- Printer of expressions -/
def printExpr : Expr → String
  | .var _ nam idx => s!"{nam}@{idx}"
  | .sort _ u => s!"(Sort {printUniv u})"
  | .const _ nam k univs => s!"{nam}@{k}.{univs.map printUniv}"
  | .app _ fnc arg => s!"({printExpr fnc} {printExpr arg})"
  | .lam _ nam binfo dom bod =>
    match binfo with
    | .implicit => s!"(λ\{{nam}: {printExpr dom}}. {printExpr bod})"
    | .strictImplicit => s!"(λ⦃{nam}: {printExpr dom}⦄. {printExpr bod})"
    | .instImplicit => s!"(λ[{nam}: {printExpr dom}]. {printExpr bod})"
    | _ => s!"(λ({nam}: {printExpr dom}). {printExpr bod})"
  | .pi _ nam binfo dom cod =>
    match binfo with
    | .implicit => s!"(\{{nam}: {printExpr dom}} → {printExpr cod})"
    | .strictImplicit => s!"(⦃{nam}: {printExpr dom}⦄ → {printExpr cod})"
    | .instImplicit => s!"([{nam}: {printExpr dom}] → {printExpr cod})"
    | _ => s!"(({nam}: {printExpr dom}) → {printExpr cod})"
  | .letE _ nam typ val bod => s!"let {nam} : {printExpr typ} := {printExpr val} in {printExpr bod}"
  | .lit _ (.natVal x) => s!"{x}"
  | .lit _ (.strVal x) => s!"\"{x}\""
  | .proj _ idx val => s!"{printExpr val}.{idx}"

mutual
  /-- Auxiliary function to print the body of a lambda expression given `env : Env` -/
  private partial def printLamBod (expr : Expr) (env : Env) : String :=
    match expr with
    | .var _ nam 0 => s!"{nam}@0"
    | .var _ nam idx =>
      match env.exprs.get? (idx-1) with
     | some val => printVal val.get
     | none => s!"!{nam}@{idx}!"
    | .sort _ u => s!"(Sort {printUniv u})"
    | .const _ nam k univs => s!"{nam}@{k}.{univs.map printUniv}"
    | .app _ fnc arg => s!"({printLamBod fnc env} {printLamBod arg env})"
    | .lam _ nam binfo dom bod =>
      match binfo with
      | .implicit => s!"(λ\{{nam}: {printLamBod dom env}}. {printLamBod bod env})"
      | .strictImplicit => s!"(λ⦃{nam}: {printLamBod dom env}⦄. {printLamBod bod env})"
      | .instImplicit => s!"(λ[{nam}: {printLamBod dom env}]. {printLamBod bod env})"
      | _ => s!"(λ({nam}: {printLamBod dom env}). {printLamBod bod env})"
    | .pi _ nam binfo dom cod =>
      match binfo with
      | .implicit => s!"(\{{nam}: {printLamBod dom env}} → {printLamBod cod env})"
      | .strictImplicit => s!"(⦃{nam}: {printLamBod dom env}⦄ → {printLamBod cod env})"
      | .instImplicit => s!"([{nam}: {printLamBod dom env}] → {printLamBod cod env})"
      | _ => s!"(({nam}: {printLamBod dom env}) → {printLamBod cod env})"
    | .letE _ nam typ val bod => s!"let {nam} : {printLamBod typ env} := {printLamBod val env} in {printLamBod bod env}"
    | .lit _ (.natVal x) => s!"{x}"
    | .lit _ (.strVal x) => s!"\"{x}\""
    | .proj _ idx val => s!"{printLamBod val env}.{idx}"

  /-- Auxiliary function to print a chain of unevaluated applications as a single application -/
  private partial def printSpine (neu : Neutral) (args : Args) : String :=
    let neu := match neu with
    | .fvar nam idx .. => s!"{nam}#{idx}"
    | .const nam k univs => s!"{nam}@{k}.{univs.map printUniv}"
    | .proj idx val => s!"{printVal val.get}.{idx}"
    List.foldr (fun arg str => s!"({str} {printVal arg.get})") neu args

  /-- Printer of typechecker values -/
  partial def printVal : Value → String
    | .sort u => s!"(Sort {printUniv u})"
    | .app neu args => printSpine neu args
    | .lam nam binfo dom bod ctx =>
      match binfo with
      | .implicit => s!"(λ\{{nam}: {printVal dom.get}}}. {printLamBod bod ctx})"
      | .strictImplicit => s!"(λ⦃{nam}: {printVal dom.get}⦄. {printLamBod bod ctx})"
      | .instImplicit => s!"(λ[{nam}: {printVal dom.get}]. {printLamBod bod ctx})"
      | _ => s!"(λ({nam}: {printVal dom.get}). {printLamBod bod ctx})"
    | .pi nam binfo dom cod ctx =>
      let dom := printVal dom.get
      match binfo with
      | .implicit => s!"(\{{nam}: {dom}} → {printLamBod cod ctx})"
      | .strictImplicit => s!"(⦃{nam}: {dom}⦄ → {printLamBod cod ctx})"
      | .instImplicit => s!"([{nam}: {dom}] → {printLamBod cod ctx})"
      | _ => s!"(({nam}: {dom}) → {printLamBod cod ctx})"
    | .lit (.natVal x) => s!"{x}"
    | .lit (.strVal x) => s!"\"{x}\""
    | .exception e => s!"exception {e}"
end

instance : ToString Expr  where toString := printExpr
instance : ToString Univ  where toString := printUniv
instance : ToString Value where toString := printVal

end Yatima.Typechecker
