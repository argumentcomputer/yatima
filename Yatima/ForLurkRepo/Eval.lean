import Yatima.ForLurkRepo.DSL
import Yatima.Compiler.Utils

namespace Lurk

open Std

inductive EnvExpr where 
  | mk : (List $ Name × EnvExpr) → Expr → EnvExpr
  deriving Repr, BEq

def EnvExpr.env (lb : EnvExpr) : (List $ Name × EnvExpr) := match lb with
  | .mk env _ => env

def EnvExpr.expr (lb : EnvExpr) : Expr := match lb with
  | .mk _ expr => expr

inductive Value where
  | lit   : Literal → Value
  | lam   : List Name → List (Name × Expr) → EnvExpr → Value
  | cons  : Value → Value → Value
  | env   : List (Name × Value) → Value
  deriving Repr, BEq, Inhabited

open Format ToFormat in
partial def Value.pprint (v : Value) (pretty := true) : Format :=
  match v with
    | .lit l => format l
    | .lam ns _ lb => paren $
      group ("lambda" ++ line ++ paren (fmtNames ns)) ++ line ++ lb.expr.pprint pretty
    | e@(.cons ..) => 
      let (es, tail) := telescopeCons [] e
      let tail := if tail == .lit .nil then 
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

instance : ToFormat Value where 
  format := Value.pprint

abbrev EvalM := ExceptT String IO

abbrev Env := RBMap Name (EnvExpr × EvalM Value) compare

def Env.getEnvExpr (env : Env) (e : Expr) : EnvExpr := ⟨env.toList.map fun (n, (lb, _)) => (n, lb), e⟩

def evalBinaryOp (op : BinaryOp) (v₁ v₂ : Value) : EvalM Value :=
  match op with
  | .sum => match v₁, v₂ with
    | .lit (.num x), .lit (.num y) => return .lit $ .num (x + y)
    | _, _ => throw "error: not a number"
  | .diff => match v₁, v₂ with
    | .lit (.num x), .lit (.num y) => return .lit $ .num (x - y)
    | _, _ => throw "error: not a number"
  | .prod => match v₁, v₂ with
    | .lit (.num x), .lit (.num y) => return .lit $ .num (x * y)
    | _, _ => throw "error: not a number"
  | .quot => match v₁, v₂ with
    | .lit (.num x), .lit (.num y) => return .lit $ .num (x * y⁻¹)
    | _, _ => throw "error: not a number"
  | .eq => match v₁, v₂ with
    | .lit (.num x), .lit (.num y) =>
      return if x == y then .lit .t else .lit .nil
    | _, _ => throw "error: not a number"
  | .nEq => return if v₁ == v₂ then .lit .t else .lit .nil

def bind (ns : List Name) (as : List Expr) :
    EvalM ((List (Name × Expr)) × List Name) := do
  let rec aux (acc : List (Name × Expr)) :
      List Name → List Expr → EvalM ((List (Name × Expr)) × List Name)
    | n::ns, a::as => aux ((n, a) :: acc) ns as
    | [], _::_ => throw "too many arguments"
    | ns, [] => return (acc, ns)
  aux [] ns as

mutual
-- Reproduce the environment needed to evaluate an `EnvExpr`.
partial def envExprToEnv (envExpr : EnvExpr) : Env :=
  envExpr.env.foldl (init := default) fun acc (n, envExpr') => acc.insert n $ (envExpr', eval (envExprToEnv envExpr') envExpr'.expr)

partial def eval (env : Env) : Expr → EvalM Value
  | .lit lit => return .lit lit
  | .sym n => match env.find? n with
    | some (_, v) => v
    | none => throw s!"{n} not found"
  | .ifE tst con alt => do
    match ← eval env tst with
    | .lit .t => eval env con
    | .lit .nil => eval env alt
    | _ => throw "not a boolean"
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
    | _ => throw "app function is not a lambda"
  | .quote _ => throw "`quote` is currently not supported"
  | .binaryOp op e₁ e₂ => do evalBinaryOp op (← eval env e₁) (← eval env e₂)
  | .atom e => return match ← eval env e with
    | .cons .. => .lit .t
    | _ => .lit .nil
  | .cons e₁ e₂ => return .cons (← eval env e₁) (← eval env e₂)
  | .strcons e₁ e₂ => do match (← eval env e₁), (← eval env e₂) with
    | .lit (.char c), .lit (.str s) => return .lit (.str ⟨c :: s.data⟩)
    | .lit (.char _), x => throw s!"expected string value, got\n {x.pprint}"
    | x, _ => throw s!"expected char value, got\n {x.pprint}"
  | .car e => do match ← eval env e with
    | .cons v _ => return v
    | .lit (.str s) => match s.data with
      | c::_ => return .lit $ .char c
      | [] => return .lit .nil
    | _ => throw "not a cons"
  | .cdr e => do match ← eval env e with
    | .cons _ v => return v
    | .lit (.str s) => match s.data with
      | _::cs => return .lit $ .str ⟨cs⟩
      | [] => return .lit $ .str ""
    | _ => throw "not a cons"
  | .emit e => do
    let v ← eval env e
    IO.println v.pprint
    pure v
  | .begin es => eval env $ es.reverse.headD $ .lit .nil
  | .currEnv => do
    let mut ret := default
    for (n, (_, e)) in env do
      ret := (n, ←e) :: ret
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
