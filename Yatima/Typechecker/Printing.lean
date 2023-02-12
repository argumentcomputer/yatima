import Yatima.Typechecker.Datatypes
import Yatima.Datatypes.PrettyPrint

/-!
# Typechecker printing

This module provides rudimentary printing for universes, expressions, and values used for debugging
the typechecker.
-/

namespace Yatima.Typechecker

open TC Lean Std.Format

private abbrev indentD := Std.Format.indentD

def TypedExpr.isProp : TypedExpr → Bool
  | .sort _ .zero => true
  | _ => false

def TypedExpr.isAtom : TypedExpr → Bool
  | .const .. | .var .. | .lit .. => true
  | .proj _ _ _ e => isAtom e
  | e => isProp e

mutual
  partial def paren (e : TypedExpr) : Format :=
    if e.isAtom then ppTypedExpr e
    else f!"({ppTypedExpr e})"

  /-- Printer of expressions -/
  partial def ppTypedExpr : TypedExpr → Format
    | .var _ idx => f!"v_{idx}"
    | .sort _ u => f!"Sort {PP.ppUniv u}"
    | .const _ k univs =>
      let us := bracket "{" (joinSep (univs.map PP.ppUniv) ", ") "}"
      f!"{k}@{us}"
    | .app _ fnc arg => match fnc with
      | .app .. => f!"{ppTypedExpr fnc} {paren arg}"
      | _ => f!"{paren fnc} {paren arg}"
    | .lam _ dom bod =>
      f!"fun (_ : {ppTypedExpr dom}) =>{indentD (ppTypedExpr bod)}"
    | .pi _ dom cod =>
      f!"((_: {ppTypedExpr dom}) → {ppTypedExpr cod})"
    | .letE _ typ val bod => f!"let _ : {ppTypedExpr typ} := {ppTypedExpr val} in {ppTypedExpr bod}"
    | .lit _ (.natVal x) => f!"{x}"
    | .lit _ (.strVal x) => f!"\"{x}\""
    | .proj _ _ idx val => f!"{ppTypedExpr val}.{idx}"

end

mutual
  /-- Auxiliary function to print the body of a lambda expression given `env : Env` -/
  private partial def printLamBod (expr : TypedExpr) (env : Env) : Format :=
    match expr with
    | .var _ 0 => f!"_@0"
    | .var _ idx =>
      match env.exprs.get? (idx-1) with
     | some val => printVal val.get
     | none => f!"!_@{idx}!"
    | .sort _ u => f!"(Sort {PP.ppUniv u})"
    | .const _ k univs => f!"_@{k}.{univs.map PP.ppUniv}"
    | .app _ fnc arg => f!"({printLamBod fnc env} {printLamBod arg env})"
    | .lam _ dom bod =>
      f!"(λ(_: {printLamBod dom env}). {printLamBod bod env})"
    | .pi _ dom cod =>
      f!"((_: {printLamBod dom env}) → {printLamBod cod env})"
    | .letE _ typ val bod => f!"let _ : {printLamBod typ env} := {printLamBod val env} in {printLamBod bod env}"
    | .lit _ (.natVal x) => f!"{x}"
    | .lit _ (.strVal x) => f!"\"{x}\""
    | .proj _ _ idx val => f!"{printLamBod val env}.{idx}"

  /-- Auxiliary function to print a chain of unevaluated applications as a single application -/
  private partial def printSpine (neu : Neutral) (args : Args) : Format :=
    let neu := match neu with
    | .fvar idx .. => f!"_#{idx}"
    | .const k univs => f!"_@{k}.{univs.map PP.ppUniv}"
    | .proj _ idx val => f!"{printVal val.value}.{idx}"
    List.foldr (fun arg str => f!"({str} {printVal arg.1.get})") neu args

  /-- Printer of typechecker values -/
  partial def printVal (val : Value) : Format :=
    match val with
    | .sort u => f!"Sort {PP.ppUniv u}"
    | .app neu args => printSpine neu args
    | .lam dom bod ctx =>
      f!"(λ(_: {printVal dom.get}). {printLamBod bod ctx})"
    | .pi dom cod ctx =>
      let dom := printVal dom.get
      f!"((_: {dom}) → {printLamBod cod ctx})"
    | .lit (.natVal x) => f!"{x}"
    | .lit (.strVal x) => f!"\"{x}\""
    | .exception e => f!"exception {e}"
end

instance : ToFormat TypedExpr where format := ppTypedExpr
instance : ToString TypedExpr where toString := pretty ∘ ppTypedExpr
instance : ToFormat Value where format := printVal
instance : ToString Value where toString := pretty ∘ printVal

end Yatima.Typechecker
