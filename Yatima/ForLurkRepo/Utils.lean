import Lean
import Yatima.ForLurkRepo.AST
import Yatima.Compiler.Utils

def Std.RBMap.filterOut [BEq α] [Ord α]
  (map : Std.RBMap α β compare) (s : Std.RBTree α compare) :
    Std.RBMap α β compare :=
  map.fold (init := default) fun acc n e' =>
    if s.contains n then acc else acc.insert n e'

namespace Lurk

namespace Expr

def mkNum (n : Nat) : Expr :=
  .lit $ .num (Fin.ofNat n)

def isNum (e : Expr) : Bool :=
  match e with | .lit $ .num _ => true | _ => false

def eqNum (e : Expr) (n : Nat) : Bool :=
  match e with | .lit $ .num m => n == m | _ => false

def mkStr (s : String) : Expr :=
  .lit $ .str s

def isStr (e : Expr) : Bool :=
  match e with | .lit $ .str _ => true | _ => false

def eqStr (e : Expr) (s₁ : String) : Bool :=
  match e with | .lit $ .str s₂ => s₁ == s₂ | _ => false

def mkIfElses (ifThens : List (Expr × Expr)) (finalElse : Expr) : Expr :=
  match ifThens with
  | [] => .lit .nil
  | [(cond, body)] => .ifE cond body finalElse
  | (cond, body) :: es => .ifE cond body (mkIfElses es finalElse)

/-- Replace all occurrences of `target` in `e` with `replacment`.-/
partial def replace (e : Expr) (target : Expr) (replacement : Expr) : Expr :=
  if e == target then
    replacement
  else match e with
    | .lit _ => e
    | .sym _ => e
    | .ifE test con alt =>
      let test := replace test target replacement
      let con := replace con target replacement
      let alt := replace alt target replacement
      .ifE test con alt
    | .lam formals body =>
      let body := replace body target replacement
      .lam formals body
    | .letE binds body =>
      let binds := binds.map fun (n, e) => (n, replace e target replacement)
      let body := replace body target replacement
      .letE binds body
    | .letRecE binds body =>
      let binds := binds.map fun (n, e) => (n, replace e target replacement)
      let body := replace body target replacement
      .letRecE binds body
    | .mutRecE binds body =>
      let binds := binds.map fun (n, e) => (n, replace e target replacement)
      let body := replace body target replacement
      .mutRecE binds body
    | .app₀ fn => .app₀ $ replace fn target replacement
    | .app fn arg =>
      let fn := replace fn target replacement
      let arg := replace arg target replacement
      .app fn arg
    | .quote _ => e
    | .binaryOp op e₁ e₂ =>
      let e₁ := replace e₁ target replacement
      let e₂ := replace e₂ target replacement
      .binaryOp op e₁ e₂
    | .cdr e => .cdr $ replace e target replacement
    | .car e => .car $ replace e target replacement
    | .atom e => .atom $ replace e target replacement
    | .emit e => .emit $ replace e target replacement
    | .cons e₁ e₂ =>
      let e₁ := replace e₁ target replacement
      let e₂ := replace e₂ target replacement
      .cons e₁ e₂
    | .strcons e₁ e₂ =>
      let e₁ := replace e₁ target replacement
      let e₂ := replace e₂ target replacement
      .strcons e₁ e₂
    | .begin es => .begin $ es.map fun e => replace e target replacement
    | .currEnv => e

/-- Given pairs `(tgtᵢ, rplᵢ)`, replaces all occurences of `tgtᵢ` with `rplᵢ`.
  This is more efficient than `replace` since one does not have to traverse
  the `Expr` tree multiple times. We do not recursively call `replaceN` on
  the newly replaced `rplᵢ` expressions. -/
partial def replaceN (e : Expr) (targets : List (Expr × Expr)) : Expr :=
  match targets.find? fun (tgt, _) => e == tgt with
  | some (_, rpl) => rpl
  | none => match e with
    | .lit _ => e
    | .sym _ => e
    | .ifE test con alt =>
      let test := replaceN test targets
      let con := replaceN con targets
      let alt := replaceN alt targets
      .ifE test con alt
    | .lam formals body =>
      let body := replaceN body targets
      .lam formals body
    | .letE binds body =>
      let binds := binds.map fun (n, e) => (n, replaceN e targets)
      let body := replaceN body targets
      .letE binds body
    | .letRecE binds body =>
      let binds := binds.map fun (n, e) => (n, replaceN e targets)
      let body := replaceN body targets
      .letRecE binds body
    | .mutRecE binds body =>
      let binds := binds.map fun (n, e) => (n, replaceN e targets)
      let body := replaceN body targets
      .mutRecE binds body
    | .app₀ fn => .app₀ $ replaceN fn targets
    | .app fn arg =>
      let fn := replaceN fn targets
      let arg := replaceN arg targets
      .app fn arg
    | .quote _ => e
    | .binaryOp op e₁ e₂ =>
      let e₁ := replaceN e₁ targets
      let e₂ := replaceN e₂ targets
      .binaryOp op e₁ e₂
    | .cdr e => .cdr $ replaceN e targets
    | .car e => .car $ replaceN e targets
    | .atom e => .atom $ replaceN e targets
    | .emit e => .emit $ replaceN e targets
    | .cons e₁ e₂ =>
      let e₁ := replaceN e₁ targets
      let e₂ := replaceN e₂ targets
      .cons e₁ e₂
    | .strcons e₁ e₂ =>
      let e₁ := replaceN e₁ targets
      let e₂ := replaceN e₂ targets
      .strcons e₁ e₂
    | .begin es => .begin $ es.map fun e => replaceN e targets
    | .currEnv => e

mutual

partial def replaceBindersFreeVars (map : Std.RBMap Name Lurk.Expr compare)
  (bindings : List (Name × Lurk.Expr))
    (rec : Bool) : List (Name × Lurk.Expr) := Id.run do
  let mut ret := []
  -- `map'` will keep track of the free vars that will be replaced if found.
  let mut map' := map
  -- as we iterate on binders, occurrences of what looked like a free variable
  -- gradually turn into bound variables with local semantics. we erase them
  -- from `map'` because we don't want to replace them
  for (n, e) in bindings do
    if rec then
      -- an occurrence of `n` in `e` can be a recursion, so we can't replace it
      -- right away
      map' := map'.erase n
      ret := (n, replaceFreeVars map' e) :: ret
    else
      -- any occurrence of `n` in `e` is definitely a free variable, so we first
      -- try to replace it
      ret := (n, replaceFreeVars map' e) :: ret
      map' := map'.erase n
  return ret.reverse

partial def replaceFreeVars (map : Std.RBMap Name Lurk.Expr compare) :
    Lurk.Expr → Lurk.Expr
  | x@(.lit _)   => x
  | x@(.quote _) => x
  | x@(.currEnv) => x
  | .sym n => match map.find? n with
    | some e => e
    | none => .sym n
  | .ifE e₁ e₂ e₃ => .ifE (replaceFreeVars map e₁)
    (replaceFreeVars map e₂) (replaceFreeVars map e₃)
  | .lam ns e => .lam ns $ replaceFreeVars (map.filterOut (.ofList ns)) e
  | .letE bindings body =>
    let map' := map.filterOut (.ofList (bindings.map (·.1)))
    .letE (replaceBindersFreeVars map bindings false) $ replaceFreeVars map' body
  | .letRecE bindings body =>
    let map' := map.filterOut (.ofList (bindings.map (·.1)))
    .letRecE (replaceBindersFreeVars map bindings true) $ replaceFreeVars map' body
  | .mutRecE bindings body =>
    let map' := map.filterOut (.ofList (bindings.map (·.1)))
    .mutRecE (replaceBindersFreeVars map bindings true) $ replaceFreeVars map' body
  | .app₀ e => .app₀ (replaceFreeVars map e)
  | .app e₁ e₂ => .app (replaceFreeVars map e₁) (replaceFreeVars map e₂)
  | .binaryOp op e₁ e₂ => .binaryOp op (replaceFreeVars map e₁) (replaceFreeVars map e₂)
  | .cons e₁ e₂ => .cons (replaceFreeVars map e₁) (replaceFreeVars map e₂)
  | .strcons e₁ e₂ => .strcons (replaceFreeVars map e₁) (replaceFreeVars map e₂)
  | .atom e => .atom (replaceFreeVars map e)
  | .car e => .car (replaceFreeVars map e)
  | .cdr e => .cdr (replaceFreeVars map e)
  | .emit e => .emit (replaceFreeVars map e)
  | .begin es => .begin $ es.map (replaceFreeVars map)

end

end Lurk.Expr

namespace Lean.Expr

def constName (e : Expr) : Name :=
  e.constName?.getD Name.anonymous

def getAppFnArgs (e : Expr) : Name × Array Expr :=
  withApp e λ e a => (e.constName, a)

/-- Converts a `Expr` of a list to a list of `Expr`s -/
partial def toListExpr (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``List.nil, #[_]) => []
  | (``List.cons, #[_, x, xs]) => x :: toListExpr xs
  | _ => []

end Lean.Expr

namespace Array

@[inline]
def concat {α : Type u} (ars : Array $ Array α) : Array α :=
  ars.foldl (init := empty) fun acc ar => acc ++ ar

end Array
