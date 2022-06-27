import Yatima.Compiler.CompileM
import Yatima.Cid

def printIsSafe (x: Bool) : String :=
  if x then "" else "unsafe "

namespace Yatima.Compiler.PrintYatima

open Yatima.Compiler.CompileM

def printDefSafety : Yatima.DefinitionSafety → String
  | .unsafe  => "unsafe "
  | .safe    => ""
  | .partial => "partial "

def getConst (constCid : ConstCid) : CompileM Const := do
  match (← get).store.const_cache.find? constCid with
  | some const => pure const
  | none => throw "Could not find constant of cid in context"

def getExpr (exprCid : ExprCid) (name : Name) : CompileM Expr := do
  match (← get).store.expr_cache.find? exprCid with
  | some expr => pure expr
  | none => throw s!"Could not find type of {name} in context"

instance : ToString QuotKind where toString
  | .type => "Quot"
  | .ctor => "Quot.mk"
  | .lift => "Quot.lift"
  | .ind  => "Quot.ind"

def get' {A: Type} : List A -> Nat -> Option A
| x::xs, 0 => some x
| x::xs, n => get' xs (n - 1)
| [], _ => none

mutual

  partial def printExternalRule (rule : ExternalRecursorRule) : CompileM String := do
    let ctor ← getConst rule.ctor
    let rhs ← getExpr rule.rhs ctor.name
    pure s!"{← printYatimaConst ctor} {rule.fields} {← printExpr rhs}"

  partial def printExternalRules (rules : List ExternalRecursorRule) : CompileM String := do
    let rules ← rules.mapM printExternalRule
    pure $ "\n".intercalate rules

  partial def printCtors (ctors : List (Name × ExprCid)) : CompileM String := do
    let ctors ← ctors.mapM fun (name, expr) => do
      let ctor ← getExpr expr name
      pure $ s!"| {name} : {← printExpr ctor}"
    pure $ "\n".intercalate ctors

  partial def printExpr : Expr → CompileM String
    | .var name idx => pure s!"{name}.{idx}"
    | .sort _ => pure "Sort"
    | .const name .. => pure s!"{name}"
    | .app func body =>
      return s!"({← printExpr func} {← printExpr body})"
    | .lam name _ type body =>
      return s!"(λ {name} : {← printExpr type}, {← printExpr body})"
    | .pi name _ type body =>
      return s!"(Π {name} : {← printExpr type}, {← printExpr body})"
    | .letE name type value body =>
      return s!"(let {name} : {← printExpr type} := {← printExpr value} in {← printExpr body})" 
    | .lit lit => return match lit with
      | .nat num => s!"{num}"
      | .str str => str
    | .lty lty => return match lty with 
      | .nat => "Nat"
      | .str => "String"
    | .fix name body => return s!"(μ {name} {← printExpr body})"
    | .proj idx expr => return s!"(proj {idx} {← printExpr expr})"

  partial def printDefinition (defn : Definition) : CompileM String := do
    let type ← getExpr defn.type defn.name
    let value ← getExpr defn.value defn.name
    return s!"{printDefSafety defn.safety}def {defn.name} {defn.lvls} : {← printExpr type} :=\n" ++
           s!"  {← printExpr value}"

  partial def printYatimaConst : Const → CompileM String
    | .axiom ax => do
      let type ← getExpr ax.type ax.name
      return s!"{printIsSafe ax.safe}axiom {ax.name} {ax.lvls} : {← printExpr type}"
    | .theorem thm => do
      let type ← getExpr thm.type thm.name
      let value ← getExpr thm.value thm.name
      return s!"theorem {thm.name} {thm.lvls} : {← printExpr type} :=\n" ++
             s!"  {← printExpr value}" 
    -- TODO: print IndBlock
    | .indBlock is => do
      return s!"TODO"
    | .inductive ind => do
      let type ← getExpr ind.type ind.name
      return s!"inductive {ind.name} {ind.lvls} : {← printExpr type} \n" ++ s!"{ind.block.anon}.{ind.block.meta}@{ind.ind}"
    | .opaque opaq => do
      let type ← getExpr opaq.type opaq.name
      let value ← getExpr opaq.value opaq.name
      return s!"{printIsSafe opaq.safe}opaque {opaq.name} {opaq.lvls} {← printExpr type} :=\n" ++
             s!"  {← printExpr value}"
    | .definition defn => printDefinition defn
    -- TODO: print actual ConstructorInfo
    | .constructor ctor => do
      let type ← getExpr ctor.type ctor.name
      let ind ← getConst ctor.block
      let ind ← match ind with
        | .indBlock is => match get' is ctor.ind with 
          | some i => pure i
          | _ => throw s!"malformed constructor with `ind` field bigger than the block it points to"
        | _ => throw s!"malformed constructor that does not point to an inductive block {ctor.block.anon}.{ctor.block.meta}"

      return s!"{printIsSafe ind.safe}constructor {ctor.name} {ctor.lvls} : {← printExpr type} :=\n" ++
             s!"  {ind.name}@{ctor.idx}"
    -- TODO: print actual RecursorInfo
    | .recursor recr => do
      let type ← getExpr recr.type recr.name
      let ind ← getConst recr.block
      let ind ← match ind with
        | .indBlock is => match get' is recr.ind with 
          | some i => pure i
          | _ => throw s!"malformed recursor with `ind` field bigger than the block it points to"
        | _ => throw s!"malformed recursor that does not point to an inductive block {recr.block.anon}.{recr.block.meta}"
      -- TODO
      --let rules ← printRules recr.externalRules
      return s!"{printIsSafe ind.safe}recursor {recr.name} {recr.lvls} : {← printExpr type} :=\n" ++
             s!"  {ind.name}@{recr.idx}"
    | .quotient quot => do
      let type ← getExpr quot.type quot.name
      return s!"quot {quot.name} {quot.lvls} : {← printExpr type} :=\n" ++
             s!"  {quot.kind}"
    | .mutDefBlock ds => do
      let defStrings ← ds.defs.join.mapM printDefinition
      return s!"mutual\n{"\n".intercalate defStrings}\nend"
    | .mutDef mutDef =>
      return s!"mutdef {mutDef.name}@{mutDef.idx} {← printYatimaConst (← getConst mutDef.block)}"

end

end Yatima.Compiler.PrintYatima

namespace Yatima.Compiler.PrintLean

open Lean

instance : ToString Lean.RecursorRule where
  toString x := s!"{x.ctor} {x.nfields} {x.rhs}"

def printDefSafety : Lean.DefinitionSafety -> String
  | .unsafe  => "unsafe "
  | .safe    => ""
  | .partial => "partial "

instance : ToString Lean.QuotKind where toString
  | .type => "Quot"
  | .ctor => "Quot.mk"
  | .lift => "Quot.lift"
  | .ind  => "Quot.ind"

def printLeanConst : Lean.ConstantInfo -> String
  | .axiomInfo  val =>
    s!"{printIsSafe !val.isUnsafe}axiom {val.name} {val.levelParams} : {val.type}"
  | .defnInfo   val =>
    s!"{printDefSafety val.safety}def {val.name} {val.levelParams} : {val.type} :=\n  {val.value}"
  | .thmInfo    val =>
    s!"theorem {val.name} {val.levelParams} : {val.type} :=\n  {val.value}"
  | .opaqueInfo val =>
    s!"{printIsSafe !val.isUnsafe}opaque {val.name} {val.levelParams} {val.type} :=\n  {val.value}"
  | .quotInfo   val =>
    s!"quot {val.name} {val.levelParams} : {val.type} :=\n  {val.kind}"
  | .inductInfo val =>
    s!"{printIsSafe !val.isUnsafe}inductive {val.name} {val.levelParams} : {val.type} :=\n" ++
    s!"  {val.numParams} {val.numIndices} {val.all} {val.ctors} {val.isRec} {val.isUnsafe} {val.isReflexive} {val.isNested}"
  | .ctorInfo   val =>
    s!"{printIsSafe !val.isUnsafe}constructor {val.name} {val.levelParams} : {val.type} :=\n" ++
    s!"  {val.induct} {val.cidx} {val.numParams} {val.numFields}"
  | .recInfo    val =>
    s!"{printIsSafe !val.isUnsafe}recursor {val.name} {val.levelParams} : {val.type} :=\n" ++
    s!"  {val.all} {val.numParams} {val.numIndices} {val.numMotives} {val.numMinors} {val.rules} {val.k}"

end Yatima.Compiler.PrintLean
