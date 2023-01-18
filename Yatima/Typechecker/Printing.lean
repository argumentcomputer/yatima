import Yatima.Typechecker.Datatypes

/-!
# Typechecker printing

This module provides rudimentary printing for universes, expressions, and values used for debugging
the typechecker.
-/

namespace Yatima.Typechecker

open TC

mutual
  /-- Printer of universe levels -/
  def printUniv (u : Univ) : String :=
    match u with
    | .succ a   => s!"{printSuccUniv 1 a}"
    | .zero     => "0"
    | .imax a b => s!"(imax {printUniv a} {printUniv b})"
    | .max  a b => s!"(max {printUniv a} {printUniv b})"
    | .var  i => s!"(_#{i})"

  def printSuccUniv (acc : Nat) : Univ → String
    | .zero => s!"{acc}"
    | .succ u => printSuccUniv (acc + 1) u
    | u => s!"{acc}+{printUniv u}"

end

/-- Printer of expressions -/
def printExpr : Expr → String
  | .var idx => s!"_@{idx}"
  | .sort u => s!"(Sort {printUniv u})"
  | .const k univs => s!"_@{k}.{univs.map printUniv}"
  | .app fnc arg => s!"({printExpr fnc} {printExpr arg})"
  | .lam dom bod =>
    s!"(λ(_: {printExpr dom}). {printExpr bod})"
  | .pi dom cod =>
    s!"((_: {printExpr dom}) → {printExpr cod})"
  | .letE typ val bod => s!"let _ : {printExpr typ} := {printExpr val} in {printExpr bod}"
  | .lit (.natVal x) => s!"{x}"
  | .lit (.strVal x) => s!"\"{x}\""
  | .proj idx val => s!"{printExpr val}.{idx}"

/-- Printer of expressions -/
def printTypedExpr : TypedExpr → String
  | .var _ idx => s!"_@{idx}"
  | .sort _ u => s!"(Sort {printUniv u})"
  | .const _ k univs => s!"_@{k}.{univs.map printUniv}"
  | .app _ fnc arg => s!"({printTypedExpr fnc} {printTypedExpr arg})"
  | .lam _ dom bod =>
    s!"(λ(_: {printTypedExpr dom}). {printTypedExpr bod})"
  | .pi _ dom cod =>
    s!"((_: {printTypedExpr dom}) → {printTypedExpr cod})"
  | .letE _ typ val bod => s!"let _ : {printTypedExpr typ} := {printTypedExpr val} in {printTypedExpr bod}"
  | .lit _ (.natVal x) => s!"{x}"
  | .lit _ (.strVal x) => s!"\"{x}\""
  | .proj _ _ idx val => s!"{printTypedExpr val}.{idx}"

mutual
  /-- Auxiliary function to print the body of a lambda expression given `env : Env` -/
  private partial def printLamBod (expr : TypedExpr) (env : Env) : String :=
    match expr with
    | .var _ 0 => s!"_@0"
    | .var _ idx =>
      match env.exprs.get? (idx-1) with
     | some val => printVal val.get
     | none => s!"!_@{idx}!"
    | .sort _ u => s!"(Sort {printUniv u})"
    | .const _ k univs => s!"_@{k}.{univs.map printUniv}"
    | .app _ fnc arg => s!"({printLamBod fnc env} {printLamBod arg env})"
    | .lam _ dom bod =>
      s!"(λ(_: {printLamBod dom env}). {printLamBod bod env})"
    | .pi _ dom cod =>
      s!"((_: {printLamBod dom env}) → {printLamBod cod env})"
    | .letE _ typ val bod => s!"let _ : {printLamBod typ env} := {printLamBod val env} in {printLamBod bod env}"
    | .lit _ (.natVal x) => s!"{x}"
    | .lit _ (.strVal x) => s!"\"{x}\""
    | .proj _ _ idx val => s!"{printLamBod val env}.{idx}"

  /-- Auxiliary function to print a chain of unevaluated applications as a single application -/
  private partial def printSpine (neu : Neutral) (args : Args) : String :=
    let neu := match neu with
    | .fvar idx .. => s!"_#{idx}"
    | .const k univs => s!"_@{k}.{univs.map printUniv}"
    | .proj _ idx val => s!"{printVal val.value}.{idx}"
    List.foldr (fun arg str => s!"({str} {printVal arg.1.get})") neu args

  /-- Printer of typechecker values -/
  partial def printVal (val : Value) : String :=
    match val with
    | .sort u => s!"(Sort {printUniv u})"
    | .app neu args => printSpine neu args
    | .lam dom bod ctx =>
      s!"(λ(_: {printVal dom.get}). {printLamBod bod ctx})"
    | .pi dom cod ctx =>
      let dom := printVal dom.get
      s!"((_: {dom}) → {printLamBod cod ctx})"
    | .lit (.natVal x) => s!"{x}"
    | .lit (.strVal x) => s!"\"{x}\""
    | .exception e => s!"exception {e}"
end

instance : ToString TypedExpr  where toString := printTypedExpr
instance : ToString Expr  where toString := printExpr
instance : ToString Univ  where toString := printUniv
instance : ToString Value where toString := printVal

end Yatima.Typechecker
