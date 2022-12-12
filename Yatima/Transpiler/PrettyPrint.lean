/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.PrettyPrinter
import Lean.Compiler.LCNF.CompilerM

open Lean Compiler.LCNF

namespace Yatima.Transpiler

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

def ppFVar (fvarId : FVarId) : Format :=
  format fvarId.name

def ppArg (e : Arg) : Format :=
  match e with
  | .erased => "◾"
  | .fvar fvarId => ppFVar fvarId
  | .type _ => "lcErasedType"

def ppArgs (args : Array Arg) : Format :=
  prefixJoin " " args ppArg

def ppLetValue (e : LetValue) : Format :=
  match e with
  | .erased => "◾"
  | .value (.natVal n) => format n
  | .value (.strVal s) => format s
  | .proj _ i fvarId => f!"{ppFVar fvarId} # {i}"
  | .fvar fvarId args => f!"{ppFVar fvarId}{ppArgs args}"
  | .const declName _ args => f!"{declName}{ppArgs args}"

def ppParam (param : Param) : Format :=
  let borrow := if param.borrow then "@&" else ""
  format s!"{borrow}{param.binderName}"

def ppParams (params : Array Param) : Format :=
  prefixJoin " " params ppParam

def ppLetDecl (letDecl : LetDecl) : Format :=
  f!"let {letDecl.binderName} := {ppLetValue letDecl.value}"

mutual
  partial def ppFunDecl (funDecl : FunDecl) : Format :=
    f!"{funDecl.binderName}{ppParams funDecl.params} : lcErasedType :={indentD (ppCode funDecl.value)}"

  partial def ppAlt (alt : Alt) : Format :=
    match alt with
    | .default k => f!"| _ =>{indentD (ppCode k)}"
    | .alt ctorName params k => f!"| {ctorName}{ppParams params} =>{indentD (ppCode k)}"

  partial def ppCode (c : Code) : Format :=
    match c with
    | .let decl k => ppLetDecl decl ++ ";" ++ .line ++ (ppCode k)
    | .fun decl k => f!"fun " ++ (ppFunDecl decl) ++ ";" ++ .line ++ (ppCode k)
    | .jp decl k => f!"jp " ++ (ppFunDecl decl) ++ ";" ++ .line ++ (ppCode k)
    | .cases c => f!"cases {ppFVar c.discr} : lcErasedType{prefixJoin .line c.alts ppAlt}"
    | .return fvarId => f!"return {ppFVar fvarId}"
    | .jmp fvarId args => f!"goto {ppFVar fvarId}{ppArgs args}"
    | .unreach _ => "⊥"
end

def ppDecl (decl : Decl) : Format :=
  f!"def {decl.name}{ppParams decl.params} : lcErasedType :={indentD (ppCode decl.value)}"

end Yatima.Transpiler