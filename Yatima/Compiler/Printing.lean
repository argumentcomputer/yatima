import Lean
import Yatima.Compiler.CompileM

def printIsSafe (x: Bool) : String :=
  if x then "" else "unsafe "

namespace Yatima.Compiler.PrintYatima

open Yatima.Compiler.CompileM

def printDefSafety : Yatima.DefinitionSafety -> String
  | .unsafe  => "unsafe "
  | .safe    => ""
  | .partial => "partial "

def getConst (const_cid : ConstCid) : CompileM Const := do
  match (← get).env.const_cache.find? const_cid with
  | some const => pure const
  | none => throw "Could not find constant of cid in context"

def getExpr (expr_cid : ExprCid) (name : Name) : CompileM Expr := do
  match (← get).env.expr_cache.find? expr_cid with
  | some expr => pure expr
  | none => throw s!"Could not find type of {name} in context"

instance : ToString QuotKind where toString
  | .type => "Quot"
  | .ctor => "Quot.mk"
  | .lift => "Quot.lift"
  | .ind  => "Quot.ind"

mutual

  partial def printRule (rule : RecursorRule) : CompileM String := do
    let ctor ← getConst rule.ctor
    let rhs ← getExpr rule.rhs ctor.name
    pure s!"{← printYatimaConst ctor} {rule.fields} {← printExpr rhs}"
  
  partial def printRules (rules : List RecursorRule) : CompileM String := do
    let rules ← rules.mapM printRule
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

  partial def printYatimaConst : Const → CompileM String
    | .axiom ax => do
      let type ← getExpr ax.type ax.name
      pure s!"{printIsSafe ax.safe}axiom {ax.name} {ax.lvls} : {← printExpr type}"
    | .theorem thm => do
      let type ← getExpr thm.type thm.name
      let value ← getExpr thm.value thm.name
      pure $ s!"theorem {thm.name} {thm.lvls} : {← printExpr type} :=\n" ++
             s!"  {← printExpr value}" 
    | .inductive ind => do
      let type ← getExpr ind.type ind.name
      pure $ s!"{printIsSafe ind.safe}inductive {ind.name} {ind.lvls} : {← printExpr type} :=\n" ++
             s!"  {ind.params} {ind.indices} {ind.recr} {ind.refl} {ind.nest}\n" ++
             s!"{← printCtors ind.ctors}"
    | .opaque opaq => do
      let type ← getExpr opaq.type opaq.name
      let value ← getExpr opaq.value opaq.name
      pure $ s!"{printIsSafe opaq.safe}opaque {opaq.name} {opaq.lvls} {← printExpr type} :=\n" ++
             s!"  {← printExpr value}"
    | .definition defn => do
      let type ← getExpr defn.type defn.name
      let value ← getExpr defn.value defn.name
      pure $ s!"{printDefSafety defn.safety}def {defn.name} {defn.lvls} : {← printExpr type} :=\n" ++
             s!"  {← printExpr value}"
    | .constructor ctor => do
      let type ← getExpr ctor.type ctor.name
      let ind ← getConst ctor.ind
      pure $ s!"{printIsSafe ctor.safe}constructor {ctor.name} {ctor.lvls} : {← printExpr type} :=\n" ++
             s!"  {ind.name} {ctor.idx} {ctor.params} {ctor.fields}"
    | .recursor recr => do
      let type ← getExpr recr.type recr.name
      let ind ← getConst recr.ind
      let rules ← printRules recr.rules
      pure $ s!"{printIsSafe recr.safe}recursor {recr.name} {recr.lvls} : {← printExpr type} :=\n" ++
             s!"  {ind.name} {recr.params} {recr.indices} {recr.motives} {recr.minors} {rules} {recr.k}"
    | .quotient quot => do
      let type ← getExpr quot.type quot.name
      pure $ s!"quot {quot.name} {quot.lvls} : {← printExpr type} :=\n" ++
             s!"  {quot.kind}"
    | .mutBlock b => sorry
    | .mutDef d   => sorry

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
