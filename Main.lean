import Lean
import Yatima.FromLean

open Yatima.Compiler.FromLean

instance : ToString Lean.RecursorRule where
  toString x := s!"{x.ctor} {x.nfields} {x.rhs}"

def prettyIsUnsafe (x: Bool) : String := if x then "unsafe " else ""
def prettyDefSafety : Lean.DefinitionSafety -> String
| .unsafe => "unsafe "
| .safe => ""
| .partial => "partial "

instance : ToString Lean.QuotKind where
  toString x := match x with
  | .type => "Quot"
  | .ctor => "Quot.mk"
  | .lift => "Quot.lift"
  | .ind => "Quot.ind"

def constantInfoToString : Lean.ConstantInfo -> String
| .axiomInfo    val =>
  s!"{prettyIsUnsafe val.isUnsafe}axiom {val.name} {val.levelParams} : {val.type}"
| .defnInfo     val =>
  s!"{prettyDefSafety val.safety}def {val.name} {val.levelParams} : {val.type} := 
  {val.value}"
| .thmInfo      val =>
  s!"theorem {val.name} {val.levelParams} : {val.type} :=
  {val.value}"
| .opaqueInfo   val =>
  s!"{prettyIsUnsafe val.isUnsafe}opaque {val.name} {val.levelParams} {val.type} := 
  {val.value}"
| .quotInfo     val =>
  s!"quot {val.name} {val.levelParams} : {val.type} := 
  {val.kind}"
| .inductInfo   val =>
  s!"{prettyIsUnsafe val.isUnsafe}inductive {val.name} {val.levelParams} : {val.type} := 
  {val.numParams} {val.numIndices} {val.all} {val.ctors} {val.isRec} {val.isUnsafe} {val.isReflexive} {val.isNested}"
| .ctorInfo     val =>
  s!"{prettyIsUnsafe val.isUnsafe}constructor {val.name} {val.levelParams} : {val.type} :=
  {val.induct} {val.cidx} {val.numParams} {val.numFields}"
| .recInfo      val =>
  s!"{prettyIsUnsafe val.isUnsafe}recursor {val.name} {val.levelParams} : {val.type} :=
  {val.all} {val.numParams} {val.numIndices} {val.numMotives} {val.numMinors} {val.rules} {val.k}"

instance : ToString Lean.ConstMap where
  toString cs :=
    let s := List.map (fun (_, y) => constantInfoToString y) cs.toList
    String.join $ List.intersperse "\n" s

def filterUnsafeConstants (cs : Lean.ConstMap) : Lean.ConstMap :=
  Lean.List.toSMap (List.filter (fun (n, c) => !c.isUnsafe) cs.toList)

def main : List String → IO UInt32
  | ["build", f] => do
    let input ← IO.FS.readFile ⟨f⟩
    Lean.initSearchPath $ ← Lean.findSysroot
    let (env, ok) ← Lean.Elab.runFrontend input .empty f `main
    --dbg_trace s!"------------"
    --dbg_trace env.constants
    dbg_trace s!"------------"
    dbg_trace (filterUnsafeConstants env.constants)
    dbg_trace s!"------------"
    if ok then
      match extractEnv (filterUnsafeConstants env.constants) with
      | .ok env => --todo
        return 0
      | .error e =>
        IO.println e
        return 1
    else
      IO.eprintln s!"Lean frontend failed on file {f}"
      return 1
  | _ => return 0
