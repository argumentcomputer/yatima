import Yatima.ForLurkRepo.DSL
import Yatima.Compiler.Utils

namespace Lurk

open Std

inductive EnvExpr where
  | mk : List (Name × EnvExpr) → Expr → EnvExpr
  deriving Repr, BEq

def EnvExpr.env : EnvExpr → List (Name × EnvExpr)
  | .mk env _ => env

def EnvExpr.expr : EnvExpr → Expr
  | .mk _ expr => expr

partial def EnvExpr.toString : EnvExpr → String 
  | .mk env expr => 
    dbg_trace s!">> toString {env.map Prod.fst}, {expr.pprint}"
    let env : List (Name × String) := env.map fun (n, ee) => (n, ee.toString)
    s!"env: {env}\nexpr: {expr.pprint}"

inductive Value where
  | lit  : Literal → Value
  | lam  : List Name → List (Name × EnvExpr × Value) → EnvExpr → Value
  | sexpr : SExpr → Value
  | cons : Value → Value → Value
  | env  : List (Name × Value) → Value
  deriving Repr, BEq, Inhabited

notation "TRUE"  => Value.lit Literal.t
notation "FALSE" => Value.lit Literal.nil

open Format ToFormat in
partial def Value.pprint (v : Value) (pretty := true) : Format :=
  match v with
    | .lit l => format l
    | .lam ns _ lb => paren $
      group ("lambda" ++ line ++ paren (fmtNames ns)) ++ line ++ lb.expr.pprint pretty
    | e@(.cons ..) =>
      let (es, tail) := telescopeCons [] e
      let tail := if tail == FALSE then
        Format.nil
      else
        line ++ "." ++ line ++ pprint tail pretty
      paren <| fmtList es ++ tail
    | .sexpr s => s.pprint
    | .env e => paren <| fmtEnv e
  where
    telescopeCons (acc : List Value) (e : Value) : List Value × Value := match e with
      | .cons e₁ e₂ => telescopeCons (e₁ :: acc) e₂
      | _ => (acc.reverse, e)
    fmtNames (xs : List Name) := match xs with
      | [ ]   => Format.nil
      | [n]   => format (fixName n pretty)
      | n::ns => format (fixName n pretty) ++ line ++ fmtNames ns
    fmtList (xs : List Value) := match xs with
      | [ ]   => Format.nil
      | [n]   => format (pprint n pretty)
      | n::ns => format (pprint n pretty) ++ line ++ fmtList ns
    fmtEnv (xs : List (Name × Value)) := match xs with
      | []         => Format.nil
      | [(n, v)]   =>
        format (fixName n pretty) ++ line ++ "." ++ line ++ format (pprint v pretty)
      | (n, v)::ns =>
        format (fixName n pretty) ++ line ++ "." ++ line ++ format (pprint v pretty) ++ line ++ fmtEnv ns

instance : ToFormat Value := ⟨Value.pprint⟩

instance : ToString Value where
  toString x := toString x.pprint

abbrev EvalM := ExceptT String IO

abbrev Env := RBMap Name (EnvExpr × EvalM Value) compare

def Env.getEnvExpr (env : Env) (e : Expr) : EnvExpr :=
  ⟨env.toList.map fun (n, (lb, _)) => (n, lb), e⟩

def num! : Value → EvalM (Fin N)
  | .lit (.num x) => pure x
  | v => throw s!"expected numerical value, got\n {v}"

def evalBinaryOp (v₁ v₂ : Value) : BinaryOp → EvalM Value
  | .sum   => return .lit $ .num $ (← num! v₁) + (← num! v₂)
  | .diff  => return .lit $ .num $ (← num! v₁) - (← num! v₂)
  | .prod  => return .lit $ .num $ (← num! v₁) * (← num! v₂)
  | .quot  => return .lit $ .num $ (← num! v₁) * (← num! v₂)⁻¹
  | .numEq => return if (← num! v₁) == (← num! v₂) then TRUE else FALSE
  | .lt    => return if (← num! v₁) <  (← num! v₂) then TRUE else FALSE
  | .gt    => return if (← num! v₁) >  (← num! v₂) then TRUE else FALSE
  | .le    => return if (← num! v₁) <= (← num! v₂) then TRUE else FALSE
  | .ge    => return if (← num! v₁) >= (← num! v₂) then TRUE else FALSE
  | .eq    => return if v₁ == v₂ then TRUE else FALSE

mutual

partial def bind (a : Expr) (env : Env) :
    List Name → EvalM ((Name × (EnvExpr × Value)) × List Name)
  | n::ns => do
    IO.println s!"[bind] {a.pprint} {n::ns}"
    let value ← evalM env a
    let envExpr := env.getEnvExpr a
    return ((n, (envExpr, value)), ns)
  | [] => throw "too many arguments"

-- Reproduce the environment needed to evaluate an `EnvExpr`.
partial def envExprToEnv (envExpr : EnvExpr) : Env :=
  -- dbg_trace s!">> envExprToEnv"
  envExpr.env.foldl (init := default) fun acc (n, envExpr') =>
    acc.insert n $ (envExpr', evalM (envExprToEnv envExpr') envExpr'.expr)

partial def evalM (env : Env) : Expr → EvalM Value
  | .lit lit => do 
    IO.println s!"[evalM] literal {format lit}"
    return .lit lit
  | .sym n => do
    IO.println s!"[evalM] symbol {n}"
    match env.find? n with
    | some (_, v) => v
    | none => throw s!"{n} not found"
  | .ifE tst con alt => do 
    IO.println s!"[evalM] if"
    match ← evalM env tst with
    | TRUE  => evalM env con
    | FALSE => evalM env alt
    | v => throw s!"expected boolean value, got\n {v}"
  | .lam formals body => do 
    IO.println s!"[evalM] lam {formals}\n{body.pprint}"
    return .lam formals [] $ env.getEnvExpr body
  | .letE bindings body => do 
    IO.println s!"[evalM] let"
    let env' ← bindings.foldlM (init := env)
      fun acc (n, e) => do
        return acc.insert n $ (acc.getEnvExpr e, pure $ ← evalM acc e)
    evalM env' body
  | .letRecE bindings body => do 
    IO.println s!"[evalM] letrec"
    let env' ← bindings.foldlM (init := env)
      fun acc (n, e) => do
        let e' := .letRecE [(n, e)] e
        -- "thunk" the result (that is, no "pure $ ←" in front)
        let acc' : Env := acc.insert n $ (acc.getEnvExpr e', evalM acc e')
        return acc.insert n $ (acc'.getEnvExpr e, pure $ ← evalM acc' e)
    evalM env' body
  | .mutRecE bindings body => do 
    IO.println s!"[evalM] mutrec"
    let env' ← bindings.foldlM (init := env)
      -- making the evaluation of every binder have access to all bindings
      fun acc (n, e) => do
        let acc' := bindings.foldl (init := acc) fun acc' (n', e') =>
          let e' := .mutRecE bindings e'
          -- "thunk" the result (that is, no "pure $ ←" in front)
          acc'.insert n' $ (acc.getEnvExpr e', evalM acc e')
        return acc.insert n $ (acc'.getEnvExpr e, pure $ ← evalM acc' e)
    evalM env' body
  | .app₀ fn => do 
    IO.println s!"[evalM] app₀"
    match fn with
    | .currEnv =>
      return .env $ ← env.foldM (init := default)
        fun acc n (_, e) => return (n, ← e) :: acc
    | _ =>
      --dbg_trace s!"[.app₀] evaluating {← evalM env fn}"
      match ← evalM env fn with
      | .lam [] [] body => evalM env body.expr
      | _ => throw "application not a procedure"
    
  | .app fn arg => do 
    IO.println s!"[evalM] app {fn.pprint} {arg.pprint}"
    dbg_trace s!"[.app] before {fn.pprint}: to {arg.pprint}"
    match ← evalM env fn with
    | .lam ns patch lb =>
      dbg_trace s!"[.app] after {fn.pprint}: {ns}, {patch.map fun (n, (_, e)) => (n, e.pprint)}}"
      let (patch', ns') ← bind arg env ns
      let patch := patch' :: patch
      if ns'.isEmpty then
        -- NOTE: `lb.env` is guaranteed not to have duplicates
        -- since it is extracted directly from an RBMap
        let ctxBinds : List (Name × (EnvExpr × Value)) ← lb.env.mapM
          fun (n, ee) => do
              -- symbols coming from the original context in which this lambda appeared must use that context
              IO.println s!">> RESURRECT {n}"
              IO.println ee.toString
              IO.println ">>"
              let env := envExprToEnv ee
              return (n, (env.getEnvExpr ee.expr, ← evalM env ee.expr))

        --dbg_trace s!"[.app] patch: {patch.map fun (n, (_, e)) => (n, e.pprint)}"
        --dbg_trace s!"[.app] ctxBinds: {ctxBinds.map fun (n, (_, e)) => (n, e.pprint)}"
        let env ← (ctxBinds.reverse ++ patch.reverse).foldlM (init := default)
          fun acc (n, (envExpr, value)) => do
            --dbg_trace s!"[.app] inserting: {n}, {value}"
            return acc.insert n (envExpr, pure value)

        -- a lambda body should be evaluated in the context of *its arguments alone* (plus whatever context it originally had)
        --dbg_trace s!"[.app] evaluating {fn.pprint}: {env.toList.map fun (name, (ee, _)) => (name, ee.expr.pprint)}, {lb.expr.pprint}"
        evalM env lb.expr
      else
        -- dbg_trace s!"[.app] not enough args {fn.pprint}: {ns'}, {patch.map fun (n, (_, e)) => (n, e.pprint)}"
        return .lam ns' patch lb
    | v => throw s!"expected lambda value, got\n {v}"
  | .quote s => do 
    IO.println s!"[evalM] quote"
    return .sexpr s
  | .binaryOp op e₁ e₂ => do 
    IO.println s!"[evalM] binop {format op}"
    evalBinaryOp (← evalM env e₁) (← evalM env e₂) op
  | .atom e => do 
    IO.println s!"[evalM] atom"
    return match ← evalM env e with
    | .cons .. => TRUE
    | _ => FALSE
  | .cons e₁ e₂ => do 
    IO.println s!"[evalM] cons {e₁.pprint} {e₂.pprint}"
    return .cons (← evalM env e₁) (← evalM env e₂)
  | .strcons e₁ e₂ => do 
    IO.println s!"[evalM] strcons"
    match (← evalM env e₁), (← evalM env e₂) with
    | .lit (.char c), .lit (.str s) => return .lit (.str ⟨c :: s.data⟩)
    | .lit (.char _), v => throw s!"expected string value, got\n {v}"
    | v, _ => throw s!"expected char value, got\n {v}"
  | .car e => do 
    IO.println s!"[evalM] car"
    match ← evalM env e with
    | .cons v _ => return v
    | .lit (.str s) => match s.data with
      | c::_ => return .lit $ .char c
      | [] => return FALSE
    | v => throw s!"expected cons value, got\n {v}"
  | .cdr e => do
    IO.println s!"[evalM] cdr"
    match ← evalM env e with
    | .cons _ v => return v
    | .lit (.str s) => match s.data with
      | _::cs => return .lit $ .str ⟨cs⟩
      | [] => return .lit $ .str ""
    | v => throw s!"expected cons value, got\n {v}"
  | .emit e => do
    IO.println s!"[evalM] emit"
    let v ← evalM env e
    IO.println v
    pure v
  | .begin es => do
    IO.println s!"[evalM] begin"
    match es.reverse.head? with
    | some e => evalM env e
    | none => return FALSE
  | .currEnv => do
    IO.println s!"[evalM] current-env"
    throw "floating `current-env`, try `(current-env)` instead"
end

def eval (e : Expr) (env : Env := default) : IO $ Except String Value :=
  return match ← evalM env e with
  | .ok res => return res
  | .error err => throw err

def ppEval (e : Expr) (env : Env := default) : IO Format :=
  return match ← evalM env e with
  | .ok res => res.pprint
  | .error e => e

instance : OfNat Value n where 
  ofNat := .lit $ .num $ Fin.ofNat n

instance : Coe Char Value where 
  coe c := .lit (.char c)

instance : Coe String Value where 
  coe s := .lit (.str s)

instance : Coe (List (Name × Nat)) Value where
  coe l := .env $ l.map fun (name, n) => (name, .lit $ .num $ Fin.ofNat n)

def Value.mkList (vs : List Value) : Value := 
  vs.foldr (fun acc v => .cons acc v) FALSE

infix:75 " .ᵥ " => Value.cons

abbrev Test := Except String Value × Expr 

end Lurk
