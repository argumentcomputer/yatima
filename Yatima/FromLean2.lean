import Yatima.Env

import Lean

def Yatima.Univ.toCid  : Univ  → ExprCid := sorry
def Yatima.Expr.toCid  : Expr  → ExprCid := sorry
def Yatima.Const.toCid : Const → ExprCid := sorry

namespace Yatima.Compiler.FromLean

instance : Coe Lean.Name Name where
  coe := Name.ofLeanName

abbrev EnvM := ReaderT Lean.ConstMap $ EStateM String Env

def toYatimaLevel (lvls : List Lean.Name) : Lean.Level → EnvM Univ
  | .zero _      => return .zero
  | .succ n _    => return .succ (← toYatimaLevel lvls n)
  | .max  a b _  => return .max  (← toYatimaLevel lvls a) (← toYatimaLevel lvls b)
  | .imax a b _  => return .imax (← toYatimaLevel lvls a) (← toYatimaLevel lvls b)
  | .param nam _ => match lvls.indexOf nam with
    | some n => return .param nam n
    | none   => throw s!"'{nam}' not found in '{lvls}'"
  | .mvar .. => throw "Unfilled level metavariable"

mutual

  partial def toYatimaRecursorRule
    (ctorCid : ConstCid) (rules : Lean.RecursorRule) :
      EnvM RecursorRule := do
    let rhs ← toYatimaExpr [] rules.rhs
    let rhsCid := rhs.toCid
    let env ← get
    set { env with exprs := env.exprs.insert rhsCid rhs }
    return ⟨ctorCid, rules.nfields, rhsCid⟩

  partial def toYatimaExpr (levelParams : List Lean.Name) :
      Lean.Expr → EnvM Expr := sorry

  partial def toYatimaConst : Lean.ConstantInfo → EnvM Const := sorry

end

end Yatima.Compiler.FromLean
