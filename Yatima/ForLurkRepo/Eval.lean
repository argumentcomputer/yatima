import Yatima.ForLurkRepo.DSL
import Yatima.Compiler.Utils

namespace Lurk

open Std

inductive Value where
  | lit  : Literal → Value
  | lam  : List Name → List (Name × Thunk Value) → (List (Name × Thunk Value)) × Expr → Value
  | sexpr : SExpr → Value
  | cons : Value → Value → Value
  | env  : List (Name × Value) → Value
  deriving Inhabited


partial def BEqVal : Value → Value → Bool
  | .lit l₁, .lit l₂ => l₁ == l₂
--| .lam ns₁ p₁ ([], b₁), .lam ns₂ p₂ ([], b₂) => ns₁ == ns₂ && (p₁.zip p₂).foldl (init := true) (fun acc ((n₁, v₁), (n₂, v₂)) => acc && n₁ == n₂ && BEqVal v₁ v₂) && b₁ == b₂
  | .lam ns₁ [] ([], b₁), .lam ns₂ [] ([], b₂) => ns₁ == ns₂ && b₁ == b₂
  | .lam .., .lam .. => false
  | .sexpr s₁, .sexpr s₂ => s₁ == s₂
  | .cons v₁ v₁', .cons v₂ v₂' => BEqVal v₁ v₂ && BEqVal v₁' v₂'
  | .env l₁ , .env l₂ => (l₁.zip l₂).foldl (init := true) (fun acc ((n₁, v₁), (n₂, v₂)) => acc && n₁ == n₂ && BEqVal v₁ v₂)
  | _, _ => false

instance : BEq Value where beq := BEqVal

notation "TRUE"  => Value.lit Literal.t
notation "FALSE" => Value.lit Literal.nil

open Format ToFormat in
partial def Value.pprint (v : Value) (pretty := true) : Format :=
  match v with
    | .lit l => format l
    | .lam ns _ (_, lb) => paren $
      group ("lambda" ++ line ++ paren (fmtNames ns)) ++ line ++ lb.pprint pretty
    | e@(.cons ..) =>
      let (es, tail) := telescopeCons [] e
      let tail := match tail with
      | .lit Literal.nil => Format.nil
      | _ => line ++ "." ++ line ++ pprint tail pretty
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

abbrev EvalM := ExceptT String $ EStateM Unit Unit

abbrev Env := RBMap Name (EvalM Value) compare

instance : Coe (EvalM Value) (Thunk Value) where coe := fun thunk =>
  .mk $ fun _ => match (EStateM.run (ExceptT.run thunk) ()) with
  | .error _ _ => default
  | .ok v _ => match v with
    | .error _ => default
    | .ok v => v

instance : Coe (Thunk Value) (EvalM Value) where coe := fun thunk => do
  pure thunk.get

def Env.getEnvExpr (env : Env) (e : Expr) : List (Name × Thunk Value) × Expr :=
  ⟨env.toList.map fun (n, v) => (n, v), e⟩

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
    List Name → EvalM ((Name × Thunk Value) × List Name)
  | n::ns => do
    --IO.println s!"[bind] {a.pprint} {n::ns}"
    let value ← evalM env a
    return ((n, value), ns)
  | [] => throw "too many arguments"

partial def evalM (env : Env) (e : Expr) : EvalM Value :=
  match e with
  | .lit lit => do 
    --IO.println s!"[evalM] literal {format lit}"
    return .lit lit
  | .sym n => do 
    --IO.println s!"[evalM] symbol {n}"
    match env.find? n with
    | some v => v
    | none => throw s!"{n} not found"
  | .ifE tst con alt => do 
    --IO.println s!"[evalM] if"
    match ← evalM env tst with
    | TRUE  => evalM env con
    | FALSE => evalM env alt
    | v => throw s!"expected boolean value, got\n {v}"
  | .lam formals body => do 
    --IO.println s!"[evalM] lam {formals}\n{body.pprint}"
    return .lam formals [] $ env.getEnvExpr body
  | .letE bindings body => do
    --IO.println s!"[evalM] let"
    let env' ← bindings.foldlM (init := env)
      fun acc (n, e) => do
        return acc.insert n $ pure $ ← evalM acc e
    evalM env' body
  | .letRecE bindings body => do 
    --IO.println s!"[evalM] letrec"
    let env' ← bindings.foldlM (init := env)
      fun acc (n, e) => do
        let e' := .letRecE [(n, e)] e
        -- "thunk" the result (that is, no `pure $ ←` in front)
        let acc' : Env := acc.insert n $ evalM acc e'
        return acc.insert n $ pure $ ← evalM acc' e
    evalM env' body
  | .mutRecE bindings body => do
    let mut env' := bindings.foldl (init := env) fun acc (n', e') =>
      let e' := .mutRecE bindings e'
      -- "thunk" the result (that is, no "pure $ ←" in front)
      acc.insert n' $ evalM env e'
    for (n, e) in bindings do
      env' := env'.insert n $ pure $ ← evalM env' e
    evalM env' body
  | .app₀ fn => do 
    --IO.println s!"[evalM] app₀"
    match fn with
    | .currEnv =>
      return .env $ ← env.foldM (init := default)
        fun acc n e => return (n, ← e) :: acc
    | _ =>
      --dbg_trace s!"[.app₀] evaluating {← evalM env fn}"
      match ← evalM env fn with
      | .lam [] [] body => evalM env body.2
      | _ => throw "application not a procedure"
    
  | .app fn arg => do 
    --IO.println s!"[evalM] app {fn.pprint} {arg.pprint}"
    -- dbg_trace s!"[.app] before {fn.pprint}: to {arg.pprint}"
    match ← evalM env fn with
    | .lam ns patch lb =>
      --dbg_trace s!"[.app] after {fn.pprint}: {ns}, {patch.map fun (n, e) => (n, e.pprint)}}"
      let (patch', ns') ← bind arg env ns
      let patch := patch' :: patch
      let patchM : List (Name × EvalM Value) := patch.map fun (n, thunk) => (n, thunk)
      if ns'.isEmpty then
        -- NOTE: `lb.env` is guaranteed not to have duplicates
        -- since it is extracted directly from an RBMap
        let ctxBinds : List (Name × EvalM Value) ← lb.1.mapM
          fun (n, ee) => do
              return (n, ee)

        --dbg_trace s!"[.app] patch: {patch.map fun (n, (_, e)) => (n, e.pprint)}"
        --dbg_trace s!"[.app] ctxBinds: {ctxBinds.map fun (n, (_, e)) => (n, e.pprint)}"
        let env ← (ctxBinds.reverse ++ patchM.reverse).foldlM (init := default)
          fun acc (n, value) => do
            --dbg_trace s!"[.app] inserting: {n}, {value}"
            return acc.insert n value

        -- a lambda body should be evaluated in the context of *its arguments alone* (plus whatever context it originally had)
        --dbg_trace s!"[.app] evaluating {fn.pprint}: {env.toList.map fun (name, (ee, _)) => (name, ee.expr.pprint)}, {lb.expr.pprint}"
        evalM env lb.2
      else
        -- dbg_trace s!"[.app] not enough args {fn.pprint}: {ns'}, {patch.map fun (n, (_, e)) => (n, e.pprint)}"
        return .lam ns' patch lb
    | v => throw s!"expected lambda value, got\n {v}"
  | .quote s => do 
    --IO.println s!"[evalM] quote"
    return .sexpr s
  | .binaryOp op e₁ e₂ => do 
    --IO.println s!"[evalM] binop {format op}"
    evalBinaryOp (← evalM env e₁) (← evalM env e₂) op
  | .atom e => do 
    --IO.println s!"[evalM] atom"
    return match ← evalM env e with
    | .cons .. => TRUE
    | _ => FALSE
  | .cons e₁ e₂ => do 
    --IO.println s!"[evalM] cons {e₁.pprint} {e₂.pprint}"
    return .cons (← evalM env e₁) (← evalM env e₂)
  | .strcons e₁ e₂ => do 
    --IO.println s!"[evalM] strcons"
    match (← evalM env e₁), (← evalM env e₂) with
    | .lit (.char c), .lit (.str s) => return .lit (.str ⟨c :: s.data⟩)
    | .lit (.char _), v => throw s!"expected string value, got\n {v}"
    | v, _ => throw s!"expected char value, got\n {v}"
  | .car e => do 
    --IO.println s!"[evalM] car"
    match ← evalM env e with
    | .cons v _ => return v
    | .lit (.str s) => match s.data with
      | c::_ => return .lit $ .char c
      | [] => return FALSE
    | v => throw s!"expected cons value, got\n {v}"
  | .cdr e => do
    --IO.println s!"[evalM] cdr"
    match ← evalM env e with
    | .cons _ v => return v
    | .lit (.str s) => match s.data with
      | _::cs => return .lit $ .str ⟨cs⟩
      | [] => return .lit $ .str ""
    | v => throw s!"expected cons value, got\n {v}"
  | .emit e => do
    --IO.println s!"[evalM] emit"
    let v ← evalM env e
    --IO.println v
    pure v
  | .begin es => do
    --IO.println s!"[evalM] begin"
    match es.reverse.head? with
    | some e => evalM env e
    | none => return FALSE
  | .currEnv => do
    --IO.println s!"[evalM] current-env"
    throw "floating `current-env`, try `(current-env)` instead"
end

def eval (e : Expr) (env : Env := default) : IO $ Except String Value := do
  match (EStateM.run (ExceptT.run (evalM env e)) ()) with
  | .ok res _ => pure res
  | .error _ _ => throw $ .otherError 0 "HERE" -- FIXME

def ppEval (e : Expr) (env : Env := default) : IO Format :=
  match (EStateM.run (ExceptT.run (evalM env e)) ()) with
  | .ok res _ => match res with
    | .ok v => pure v.pprint
    | .error s => throw $ .otherError 0 s -- FIXME
  | .error _ _ => throw $ .otherError 0 "HERE" -- FIXME

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

-- #eval ppEval ⟦
-- (letrec
-- ((getelem
--   (lambda (xs n)
--    (if (= n 0)
--     (car xs)
--     ((getelem (cdr xs)) (- n 1))))))
--  (getelem (cons 1 nil) 1))⟧

-- this one is very strange
#eval ppEval ⟦(letrec ((exp (lambda (base) (lambda (exponent)
                  (if (= 0 exponent)
                      1
                      (* base ((exp base) (- exponent 1))))))))
            (let ((myexp exp) (exp (lambda (base) (lambda (exponent) 10)))) ((myexp 5) 3)))⟧

end Lurk
