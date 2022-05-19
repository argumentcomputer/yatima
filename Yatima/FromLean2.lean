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

  partial def toYatimaConst : Lean.ConstantInfo → EnvM Const
    | .axiomInfo struct => do
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid := type.toCid
      let env ← get
      set { env with exprs := env.exprs.insert typeCid type }
      return Yatima.Const.axiom {
        name := struct.name
        lvls := struct.levelParams.map Yatima.Name.ofLeanName
        type := typeCid
        safe := not struct.isUnsafe }
    | .thmInfo struct =>
      return Yatima.Const.theorem {
        name  := struct.name
        lvls  := struct.levelParams.map Yatima.Name.ofLeanName
        type  := ← toYatimaExpr constMap struct.levelParams struct.type
        value := ← toYatimaExpr constMap struct.levelParams struct.value }
    | .opaqueInfo struct =>
      return Yatima.Const.opaque {
        name  := struct.name
        lvls  := struct.levelParams.map Yatima.Name.ofLeanName
        type  := ← toYatimaExpr constMap struct.levelParams struct.type
        value := ← toYatimaExpr constMap struct.levelParams struct.value
        safe  := not struct.isUnsafe }
    | .defnInfo struct =>
      return Yatima.Const.definition {
        name   := struct.name
        lvls   := struct.levelParams.map Yatima.Name.ofLeanName
        type   := ← toYatimaExpr constMap struct.levelParams struct.type
        value  := ← toYatimaExpr constMap struct.levelParams struct.value
        safety := struct.safety }
    | .ctorInfo struct =>
      return Yatima.Const.constructor {
        name := struct.name
        lvls := struct.levelParams.map Yatima.Name.ofLeanName
        type := ← toYatimaExpr constMap struct.levelParams struct.type
        ind  := sorry
        idx  := struct.cidx
        params := struct.numParams
        fields := struct.numFields
        safe := not struct.isUnsafe }
    | .inductInfo struct =>
      return Yatima.Const.inductive {
        name := struct.name
        lvls := struct.levelParams.map Yatima.Name.ofLeanName
        type := ← toYatimaExpr constMap struct.levelParams struct.type
        params := struct.numParams
        indices := struct.numIndices
        ctors := struct.ctors.map Yatima.Name.ofLeanName
        recr := struct.isRec
        refl := struct.isReflexive
        nest := struct.isNested
        safe := not struct.isUnsafe }
    | .recInfo struct =>
      return Yatima.Const.recursor {
        name := struct.name
        lvls := struct.levelParams.map Yatima.Name.ofLeanName
        type := ← toYatimaExpr constMap struct.levelParams struct.type
        params := struct.numParams
        ind := sorry
        motives := struct.numMotives
        indices := struct.numIndices
        minors := struct.numMinors
        rules := ← struct.rules.mapM (toYatimaRecursorRule constMap)
        k := struct.k
        safe := not struct.isUnsafe }
    | .quotInfo struct => do
      pure $ Yatima.Const.quotient {
        name := struct.name
        lvls := struct.levelParams.map Yatima.Name.ofLeanName
        type := ← toYatimaExpr constMap struct.levelParams struct.type
        kind := struct.kind }

end

end Yatima.Compiler.FromLean
