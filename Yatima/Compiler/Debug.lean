import Lean.Compiler.LCNF
open Lean.Compiler.LCNF

namespace Lean.Compiler.LCNF

instance : ToString FVarId where
  toString x := toString x.name

instance : ToString Param where
  toString x := s!"{x.fvarId}"

instance [ToString K] : ToString (AltCore K) where
  toString
    | .alt ctor params k => s!"{ctor} {params} => {k}"
    | .default k => s!"_ => {k}"

instance : ToString LitValue where
  toString
  | .natVal x => s!"{x}"
  | .strVal x => s!"\"{x}\""

instance : ToString Arg where
  toString
  | .erased => "ε"
  | .type .. => "τ"
  | .fvar id => s!"{id}"

instance : ToString LetValue where
  toString
    | .value lit => s!"{lit}"
    | .erased .. => "ε"
    | .proj _ idx struct => s!"(π {idx} {struct})"
    | .const cnst _ args => s!"(const {cnst} {args})"
    | .fvar id args => s!"(fvar {id} {args})"

instance : ToString LetDecl where
  toString decl := s!"{decl.fvarId} := {decl.value}"

instance [ToString K] : ToString (FunDeclCore K) where
  toString decl := s!"{decl.fvarId} {decl.params} := {decl.value}"

instance [ToString K] : ToString (CasesCore K) where
  toString cases := s!"{cases.discr} {cases.alts}"

partial def Code.toString (code : Code) : String :=
  let _ : ToString Code := ⟨toString⟩
  match code with
  | .let decl k => s!"(let {decl} in {k})"
  | .fun decl k => s!"(fun {decl} in {k})"
  | .jp decl k => s!"(jp {decl} in {k})"
  | .jmp id args => s!"(jmp {id} {args})"
  | .cases case => s!"(match {case})"
  | .return id => s!"(return {id.name})"
  | .unreach _ => "unreach"

instance : ToString Code where
  toString code := code.toString

end Lean.Compiler.LCNF
