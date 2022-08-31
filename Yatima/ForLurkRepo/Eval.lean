import Yatima.ForLurkRepo.DSL
import Yatima.Compiler.Utils

namespace Lurk
open Std 

inductive Value where
  | lit : Literal → Value
  | lam : List Name → Expr → Value
  | raw : SExpr → Value
  | env : List (Name × Value) → Value
  deriving Repr, BEq, Inhabited

abbrev Env := Std.RBMap Name Value compare

open Std.Format Std.ToFormat in
partial def Value.pprint (v : Value) (pretty := true) : Std.Format :=
  match v with
    | .lit l => format l
    | .lam ns e => paren $
      group ("lambda" ++ line ++ paren (fmtNames ns)) ++ line ++ e.pprint pretty
    | .raw s => s.pprint pretty
    | .env e => sorry
  where 
    fmtNames (xs : List Name) := match xs with 
      | [] => Format.nil
      | [n]  => format $ fixName n pretty
      | n::ns => format (fixName n pretty) ++ line ++ fmtNames ns

instance : ToFormat Value where 
  format := Value.pprint

abbrev EvalM := ExceptT String IO

def evalUnaryOp (op : UnaryOp) (v : Value) : EvalM Value :=
  match op with
  | .car => default  
  | .cdr => default
  | .atom => default
  | .emit => default

def evalBinaryOp (op : BinaryOp) (v₁ v₂ : Value) : EvalM Value :=
  match op with
  | .cons => default
  | .strcons => default
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

def bind (body : Expr) (ns : List Name) (as : List Expr) :
    EvalM (Expr × List Name) := do
  let rec aux (acc : List (Name × Expr)) :
      List Name → List Expr → EvalM ((List (Name × Expr)) × List Name)
    | n::ns, a::as => aux ((n, a) :: acc) ns as
    | [], _::_ => throw "too many arguments"
    | ns, [] => return (acc, ns)
  let (binds, ns') ← aux [] ns as
  return (.letE binds body, ns')

partial def evalM (env : Env) : Expr → EvalM Value
  | .lit lit => return .lit lit
  | .sym n => match env.find? n with
    | some v => return v
    | none => throw s!"{n} not found"
  | .ifE tst con alt => do
    match ← evalM env tst with
    | .lit .t => evalM env con
    | .lit .nil => evalM env alt
    | _ => throw "not a boolean"
  | .lam formals body => return .lam formals body
  | .letE bindings body => do
    let env' ← bindings.foldlM (init := env)
      fun acc (n, e) => return acc.insert n (← evalM acc e)
    evalM env' body
  | .letRecE bindings body => default
  | .app fn args => do
    match ← evalM env fn with
    | .lam ns body =>
      let (body', ns') ← bind body ns args
      if ns'.isEmpty then evalM env body' else return .lam ns body'
    | _ => throw "app function is not a lambda"
  | .quote datum => default 
  | .unaryOp op e => do evalUnaryOp op (← evalM env e)
  | .binaryOp op e₁ e₂ => do evalBinaryOp op (← evalM env e₁) (← evalM env e₂)
  | .emit e => do
    let v ← evalM env e
    IO.println v.pprint
    pure v
  | .begin es => default
  | .currEnv => return .env env.toList
  | .eval e env? => do match ← evalM default (env?.getD default) with
    | .env bs => evalM (.ofList bs) e
    | _ => throw "env expression did not evaluate to a proper environment"

def evalPP (e : Expr) (env : Env := default) : IO Format :=
  return match ← evalM env e with
  | .ok res => res.pprint 
  | .error e => e

#eval ⟦,1⟧

end Lurk 