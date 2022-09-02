import Yatima.ForLurkRepo.DSL
import Yatima.Compiler.Utils

namespace Lurk

open Std

inductive EnvExpr where
  | mk : (List $ Name × EnvExpr) → Expr → EnvExpr
  deriving Repr, BEq

def EnvExpr.env : EnvExpr → (List $ Name × EnvExpr)
  | .mk env _ => env

def EnvExpr.expr : EnvExpr → Expr
  | .mk _ expr => expr

inductive Value where
  | lit   : Literal → Value
  | lam   : List Name → List (Name × Expr) → EnvExpr → Value
  | cons  : Value → Value → Value
  | env   : List (Name × Value) → Value
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

instance : Coe Bool Value where coe
  | true  => TRUE
  | false => FALSE

def evalBinaryOp (v₁ v₂ : Value) : BinaryOp → EvalM Value
  | .sum  => return .lit $ .num $ (← num! v₁) + (← num! v₂)
  | .diff => return .lit $ .num $ (← num! v₁) - (← num! v₂)
  | .prod => return .lit $ .num $ (← num! v₁) * (← num! v₂)
  | .quot => return .lit $ .num $ (← num! v₁) * (← num! v₂)⁻¹
  | .eq => match v₁, v₂ with
    | .lit l₁, .lit l₂ => return l₁ == l₂
    | _, _ => return FALSE
  | .nEq => return v₁ == v₂

def bind (ns : List Name) (as : List Expr) :
    EvalM ((List (Name × Expr)) × List Name) :=
  let rec aux (acc : List (Name × Expr)) :
      List Name → List Expr → EvalM ((List (Name × Expr)) × List Name)
    | n::ns, a::as => aux ((n, a) :: acc) ns as
    | [], _::_ => throw "too many arguments"
    | ns, [] => return (acc, ns)
  aux [] ns as

mutual

-- Reproduce the environment needed to evaluate an `EnvExpr`.
partial def envExprToEnv (envExpr : EnvExpr) : Env :=
  envExpr.env.foldl (init := default) fun acc (n, envExpr') =>
    acc.insert n $ (envExpr', eval (envExprToEnv envExpr') envExpr'.expr)

partial def eval (env : Env) : Expr → EvalM Value
  | .lit lit => return .lit lit
  | .sym n => match env.find? n with
    | some (_, v) => v
    | none => throw s!"{n} not found"
  | .ifE tst con alt => do
    match ← eval env tst with
    | TRUE  => eval env con
    | FALSE => eval env alt
    | v => throw s!"expected boolean value, got\n {v}"
  | .lam formals body => return .lam formals [] $ env.getEnvExpr body
  | .letE bindings body => do
    let env' ← bindings.foldlM (init := env)
      fun acc (n, e) => do
        return acc.insert n $ (acc.getEnvExpr e, pure $ ← eval acc e)
    eval env' body
  | .letRecE bindings body => do
    let env' ← bindings.foldlM (init := env)
      fun acc (n, e) => do
        let e' := (.letRecE [(n, e)] e)
        -- "thunk" the result (that is, no "pure $ ←" in front)
        let acc' : Env := acc.insert n $ (acc.getEnvExpr e', eval acc e')
        return acc.insert n $ (acc'.getEnvExpr e, pure $ ← eval acc' e)
    eval env' body
  | .app fn args => do
    match ← eval env fn with
    | .lam ns patch lb =>
      let (patch', ns') ← bind ns args
      let patch := patch' ++ patch
      if ns'.isEmpty then
        -- NOTE: `lb.env` is guaranteed not to have duplicates
        -- since it is extracted directly from an RBMap
        -- FIXME "some ee"
        let (env, _) ← (patch.map (·, none) ++ (lb.env.map (fun (n, ee) => ((n, ee.expr), some ee))) : List ((Name × Expr) × Option EnvExpr)).reverse.foldlM (init := (default, env))
          fun (acc, acc') ((n, e), env?) => do
            let env :=
              match env? with
              -- arguments are free to use the current context
              | none => acc'
              -- symbols coming from the original context in which this lambda appeared must use that context
              | some envExpr => envExprToEnv envExpr
            let value ← eval env e
            let envExpr := env.getEnvExpr e
            return (acc.insert n (envExpr, pure value), acc'.insert n (envExpr, pure value))

        -- a lambda body should be evaluated in the context of *its arguments alone* (plus whatever context it originally had)
        eval env lb.expr
      else return .lam ns' patch lb
    | .env env =>
      if args.isEmpty then return .env env else throw "too many arguments"
    | v => throw s!"expected lambda value, got\n {v}"
  | .quote _ => throw "`quote` is currently not supported"
  | .binaryOp op e₁ e₂ => do evalBinaryOp (← eval env e₁) (← eval env e₂) op
  | .atom e => return match ← eval env e with
    | .cons .. => TRUE
    | _ => FALSE
  | .cons e₁ e₂ => return .cons (← eval env e₁) (← eval env e₂)
  | .strcons e₁ e₂ => do match (← eval env e₁), (← eval env e₂) with
    | .lit (.char c), .lit (.str s) => return .lit (.str ⟨c :: s.data⟩)
    | .lit (.char _), v => throw s!"expected string value, got\n {v}"
    | v, _ => throw s!"expected char value, got\n {v}"
  | .car e => do match ← eval env e with
    | .cons v _ => return v
    | .lit (.str s) => match s.data with
      | c::_ => return .lit $ .char c
      | [] => return FALSE
    | v => throw s!"expected cons value, got\n {v}"
  | .cdr e => do match ← eval env e with
    | .cons _ v => return v
    | .lit (.str s) => match s.data with
      | _::cs => return .lit $ .str ⟨cs⟩
      | [] => return .lit $ .str ""
    | v => throw s!"expected cons value, got\n {v}"
  | .emit e => do
    let v ← eval env e
    IO.println v
    pure v
  | .begin es => eval env $ es.reverse.headD $ .lit .nil
  | .currEnv => do
    let mut ret := default
    for (n, (_, e)) in env do
      ret := (n, ← e) :: ret
    return .env ret
end

def ppEval (e : Expr) (env : Env := default) : IO Format :=
  return match ← eval env e with
  | .ok res => res.pprint
  | .error e => e

#eval ppEval ⟦(letrec ((exp (lambda (base exponent)
                 (if (= 0 exponent)
                     1
                     (* base (exp base (- exponent 1)))))))
         (exp 2 4))⟧

end Lurk
