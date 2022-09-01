import Yatima.ForLurkRepo.DSL
import Yatima.Compiler.Utils

namespace Lurk
open Std 

inductive Value where
  | lit  : Literal → Value
  | lam  : List Name → Expr → Value
  | cons : Value → Value → Value
  | env  : List (Name × Value) → Value
  deriving Repr, BEq, Inhabited

abbrev Env := Std.RBMap Name Value compare

open Std.Format Std.ToFormat in
partial def Value.pprint (v : Value) (pretty := true) : Std.Format :=
  match v with
    | .lit l => format l
    | .lam ns e => paren $
      group ("lambda" ++ line ++ paren (fmtNames ns)) ++ line ++ e.pprint pretty
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
      | [ ]        => Format.nil
      | [(n, v)]   => 
        format (fixName n pretty) ++ line ++ "." ++ line ++ format (pprint v pretty)
      | (n, v)::ns => 
        format (fixName n pretty) ++ line ++ "." ++ line ++ format (pprint v pretty) ++ line ++ fmtEnv ns

instance : ToFormat Value where 
  format := Value.pprint

abbrev EvalM := ExceptT String IO

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

def bind (body : Expr) (ns : List Name) (as : List Expr) :
    EvalM (Expr × List Name) := do
  let rec aux (acc : List (Name × Expr)) :
      List Name → List Expr → EvalM ((List (Name × Expr)) × List Name)
    | n::ns, a::as => aux ((n, a) :: acc) ns as
    | [], _::_ => throw "too many arguments"
    | ns, [] => return (acc, ns)
  let (binds, ns') ← aux [] ns as
  return (.letE binds body, ns')

def isAtom (e : Expr) : Bool := match e with 
  | .cons .. => false 
  | _ => true

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
  | .quote _ => unreachable! -- not used for debugging/testing
  | .binaryOp op e₁ e₂ => do evalBinaryOp op (← evalM env e₁) (← evalM env e₂)
  | .atom e => if isAtom e then return .lit .t else return .lit .nil
  | .cons e₁ e₂ => return .cons (← evalM env e₁) (← evalM env e₂)
  | .strcons e₁ e₂ => do match (← evalM env e₁), (← evalM env e₂) with 
    | .lit (.char c), .lit (.str s) => return .lit (.str ⟨c :: s.data⟩)
    | .lit (.char _), x => throw s!"expected string value, got\n {x.pprint}" 
    | x, _ => throw s!"expected char value, got\n {x.pprint}" 
  | .car e => do match (← evalM env e) with 
    | .cons e₁ _ => return e₁ 
    | _ => throw "not a cons"
  | .cdr e => do match (← evalM env e) with 
    | .cons e₁ _ => return e₁ 
    | _ => throw "not a cons"
  | .emit e => do
    let v ← evalM env e
    IO.println v.pprint
    pure v
  | .begin es => evalM env $ es.reverse.headD $ .lit .nil
  | .currEnv => return .env env.toList

def ppEval (e : Expr) (env : Env := default) : IO Format :=
  return match ← evalM env e with
  | .ok res => res.pprint 
  | .error e => e

end Lurk
