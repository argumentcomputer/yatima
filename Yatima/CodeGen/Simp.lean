import Lurk.Expr

namespace Lurk.Expr

def simpStep : Expr → Expr
  | .app (.app (.sym "Nat.add") x) y => .op₂ .add x.simpStep y.simpStep
  | .app (.app (.sym "Nat.mul") x) y => .op₂ .mul x.simpStep y.simpStep
  | .app (.sym "Int.ofNat") x => x.simpStep
  | .op₁ op e => .op₁ op e.simpStep
  | .op₂ op e₁ e₂ => .op₂ op e₁.simpStep e₂.simpStep
  | .begin e₁ e₂ => .begin e₁.simpStep e₂.simpStep
  | .if e₁ e₂ e₃ => .if e₁.simpStep e₂.simpStep e₃.simpStep
  | .app₀ e => .app₀ e.simpStep
  | .app e₁ e₂ => .app e₁.simpStep e₂.simpStep
  | .lambda s b => .lambda s b.simpStep
  | .let s v b => .let s v.simpStep b.simpStep
  | .letrec s v b => .letrec s v.simpStep b.simpStep
  | x => x

partial def simp (e : Expr) : Expr :=
  let e' := e.simpStep
  if e' == e then e else e'.simp

end Lurk.Expr
