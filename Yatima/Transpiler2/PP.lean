/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.PrettyPrinter
import Yatima.Transpiler2.TranspileM
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.Internalize

open Lean Compiler.LCNF

namespace Yatima.Transpiler2

private abbrev indentD := Std.Format.indentD

abbrev M := TranspileM
private def join (as : Array α) (f : α → M Format) : M Format := do
  if h : 0 < as.size then
    let mut result ← f as[0]
    for a in as[1:] do
      result := f!"{result} {← f a}"
    return result
  else
    return .nil

private def prefixJoin (pre : Format) (as : Array α) (f : α → M Format) : M Format := do
  let mut result := .nil
  for a in as do
    result := f!"{result}{pre}{← f a}"
  return result

def ppFVar (fvarId : FVarId) : M Format :=
  try
    return format (← getBinderName fvarId)
  catch _ =>
    return format fvarId.name

def ppArg (e : Arg) : M Format := do
  match e with
  | .erased => return "◾"
  | .fvar fvarId => ppFVar fvarId
  | .type _ => return "lcErasedType"

def ppArgs (args : Array Arg) : M Format := do
  prefixJoin " " args ppArg

def ppLetValue (e : LetValue) : M Format := do
  match e with
  | .erased => return "◾"
  | .value (.natVal n) => return format n
  | .value (.strVal s) => return format s
  | .proj _ i fvarId => return f!"{← ppFVar fvarId} # {i}"
  | .fvar fvarId args => return f!"{← ppFVar fvarId}{← ppArgs args}"
  | .const declName us args => return f!"{declName}{← ppArgs args}"

def ppParam (param : Param) : M Format := do
  let borrow := if param.borrow then "@&" else ""
  return format s!"{borrow}{param.binderName}"

def ppParams (params : Array Param) : M Format := do
  prefixJoin " " params ppParam

def ppLetDecl (letDecl : LetDecl) : M Format := do
  return f!"let {letDecl.binderName} := {← ppLetValue letDecl.value}"

def getFunType (ps : Array Param) (type : Expr) : CoreM Expr :=
  instantiateForall type (ps.map (mkFVar ·.fvarId))

mutual
  partial def ppFunDecl (funDecl : FunDecl) : M Format := do
    return f!"{funDecl.binderName}{← ppParams funDecl.params} : lcErasedType :={indentD (← ppCode funDecl.value)}"

  partial def ppAlt (alt : Alt) : M Format := do
    match alt with
    | .default k => return f!"| _ =>{indentD (← ppCode k)}"
    | .alt ctorName params k => return f!"| {ctorName}{← ppParams params} =>{indentD (← ppCode k)}"

  partial def ppCode (c : Code) : M Format := do
    match c with
    | .let decl k => return (← ppLetDecl decl) ++ ";" ++ .line ++ (← ppCode k)
    | .fun decl k => return f!"fun " ++ (← ppFunDecl decl) ++ ";" ++ .line ++ (← ppCode k)
    | .jp decl k => return f!"jp " ++ (← ppFunDecl decl) ++ ";" ++ .line ++ (← ppCode k)
    | .cases c => return f!"cases {← ppFVar c.discr} : lcErasedType{← prefixJoin .line c.alts ppAlt}"
    | .return fvarId => return f!"return {← ppFVar fvarId}"
    | .jmp fvarId args => return f!"goto {← ppFVar fvarId}{← ppArgs args}"
    | .unreach type => return "⊥"
end

def ppDecl (decl : Decl) : M Format :=
  return f!"def {decl.name}{← ppParams decl.params} : lcErasedType :={indentD (← ppCode decl.value)}"

end Yatima.Transpiler2