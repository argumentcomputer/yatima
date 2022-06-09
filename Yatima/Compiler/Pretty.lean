import Yatima.Compiler.FromLean

import Lean

namespace Yatima.Compiler.FromLean

def prettyIsSafe (x: Bool) : String :=
  if x then "" else "unsafe "

def prettyDefSafety : Yatima.DefinitionSafety -> String
  | .unsafe => "unsafe "
  | .safe => ""
  | .partial => "partial "

def getConst (const_cid : ConstCid) : CompileM Const := do
  match (← get).env.const_cache.find? const_cid with
  | some const => pure const
  | none => throw s!"Could not find constant of cid in context"

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

  partial def prettyRule (rule : RecursorRule) : CompileM String := do
    let ctor ← getConst rule.ctor
    let rhs ← getExpr rule.rhs ctor.name
    pure s!"{← prettyConst ctor} {rule.fields} {← prettyExpr rhs}"
  
  partial def prettyRules (rules : List RecursorRule) : CompileM String := do
    let rules ← rules.mapM prettyRule
    pure $ String.join $ rules.intersperse "\n"
  
  partial def prettyCtors (ctors : List (Name × ExprCid)) : CompileM String := do
    let ctors ← ctors.mapM fun (name, expr) => do
      let ctor ← getExpr expr name
      pure $ s!"| {name} : {← prettyExpr ctor}"
    
    pure $ String.join $ ctors.intersperse "\n"

  partial def prettyExpr (expr : Expr) : CompileM String := do
    match expr with 
    | .var name idx => pure s!"{name}.{idx}"
    | .sort _ => pure "Sort"
    | .const name .. => pure s!"{name}"
    | .app func body => do
      pure s!"({← prettyExpr func} {← prettyExpr body})"
    | .lam name _ type body =>
      pure s!"(λ {name} : {← prettyExpr type}, {← prettyExpr body})"
    | .pi name _ type body =>
      pure s!"(Π {name} : {← prettyExpr type}, {← prettyExpr body})"
    | .letE name type value body =>
      pure s!"(let {name} : {← prettyExpr type} := {← prettyExpr value} in {← prettyExpr body})" 
    | .lit lit =>
      match lit with
        | .nat num => pure s!"num"
        | .str str => pure str
    | .lty lty => 
      match lty with 
      | .nat => pure "Nat"
      | .str => pure "String"
    | .fix name body => 
      pure s!"(μ {name} {← prettyExpr body})"
    | .proj idx expr => pure s!"(proj {idx} {← prettyExpr expr})"

  partial def prettyConst (const : Const) : CompileM String := do
    match const with 
    | .axiom ax => do
      let type ← getExpr ax.type ax.name
      pure s!"{prettyIsSafe ax.safe}axiom {ax.name} {ax.lvls} : {← prettyExpr type}"
    | .theorem thm => do
      let type ← getExpr thm.type thm.name
      let value ← getExpr thm.value thm.name
      pure $ s!"theorem {thm.name} {thm.lvls} : {← prettyExpr type} :=\n" ++
             s!"  {← prettyExpr value}" 
    | .inductive ind => do
      let type ← getExpr ind.type ind.name
      pure $ s!"{prettyIsSafe ind.safe}inductive {ind.name} {ind.lvls} : {← prettyExpr type} :=\n" ++
             s!"  {ind.params} {ind.indices} {ind.recr} {ind.refl} {ind.nest}\n" ++
             s!"{← prettyCtors ind.ctors}"
    | .opaque opaq => do
      let type ← getExpr opaq.type opaq.name
      let value ← getExpr opaq.value opaq.name
      pure $ s!"{prettyIsSafe opaq.safe}opaque {opaq.name} {opaq.lvls} {← prettyExpr type} :=\n" ++
             s!"  {← prettyExpr value}"
    | .definition defn => do
      let type ← getExpr defn.type defn.name
      let value ← getExpr defn.value defn.name
      pure $ s!"{prettyDefSafety defn.safety}def {defn.name} {defn.lvls} : {← prettyExpr type} :=\n" ++
             s!"  {← prettyExpr value}"
    | .constructor ctor => do
      let type ← getExpr ctor.type ctor.name
      let ind ← getConst ctor.ind
      pure $ s!"{prettyIsSafe ctor.safe}constructor {ctor.name} {ctor.lvls} : {← prettyExpr type} :=\n" ++
             s!"  {ind.name} {ctor.idx} {ctor.params} {ctor.fields}"
    | .recursor recr => do
      let type ← getExpr recr.type recr.name
      let ind ← getConst recr.ind
      let rules ← prettyRules recr.rules
      pure $ s!"{prettyIsSafe recr.safe}recursor {recr.name} {recr.lvls} : {← prettyExpr type} :=\n" ++
             s!"  {ind.name} {recr.params} {recr.indices} {recr.motives} {recr.minors} {rules} {recr.k}"
    | .quotient quot => do
      let type ← getExpr quot.type quot.name
      pure $ s!"quot {quot.name} {quot.lvls} : {← prettyExpr type} :=\n" ++
             s!"  {quot.kind}"

end

-- unduplicate later
def buildAndPrintEnv (constMap : Lean.ConstMap) : CompileM Env := do
  constMap.forM fun _ leanConst => do
    dbg_trace s!"Processing: {leanConst.name}"
    let yatimaConst ← toYatimaConst leanConst
    dbg_trace s!"{← prettyConst yatimaConst}\n\n"
    let constCid ← constToCid yatimaConst
    addToEnv $ .const_cache constCid yatimaConst
  return (← get).env

def extractAndPrintEnv (constMap : Lean.ConstMap) : Except String Env :=
  CompileM.run (CompileEnv.mk constMap []) default (buildAndPrintEnv constMap)

end Yatima.Compiler.FromLean
