import Yatima.Env

import Lean

def Yatima.Univ.toCid  : Univ  → UnivCid  := sorry
def Yatima.Expr.toCid  : Expr  → ExprCid  := sorry
def Yatima.Const.toCid : Const → ConstCid := sorry

namespace Yatima.Compiler.FromLean

instance : Coe Lean.Name Name where
  coe := .ofLeanName

instance : Coe Lean.BinderInfo BinderInfo where coe
  | .default        => .default
  | .auxDecl        => .auxDecl
  | .instImplicit   => .instImplicit
  | .strictImplicit => .strictImplicit
  | .implicit       => .implicit

instance : Coe Lean.Literal Literal where coe
  | .natVal n => .nat n
  | .strVal s => .str s

instance : Coe Lean.DefinitionSafety DefinitionSafety where coe
  | .safe      => .safe
  | .«unsafe»  => .«unsafe»
  | .«partial» => .«partial»

instance : Coe Lean.QuotKind QuotKind where coe
  | .type => .type
  | .ind  => .ind
  | .lift => .lift
  | .ctor => .ctor

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
      Lean.Expr → EnvM Expr
    | .bvar idx _ => return .var "" idx
    | .sort lvl _ =>
      return .sort (← toYatimaLevel levelParams lvl)
    | .const nam lvls _ => do
      match (← read).find?' nam with
      | some const => return .const nam (← lvls.mapM $ toYatimaLevel levelParams)
      | none => throw "Unknown constant"
    | .app fnc arg _ => do
      let fnc ← toYatimaExpr levelParams fnc
      let arg ← toYatimaExpr levelParams arg
      return .app fnc arg
    | .lam nam bnd bod _ => do
      let bndInfo := bnd.binderInfo
      let bnd ← toYatimaExpr levelParams bnd
      let bod ← toYatimaExpr levelParams bod
      return .lam nam bndInfo bnd bod
    | .forallE nam dom img _ => do
      let bndInfo := dom.binderInfo
      let dom ← toYatimaExpr levelParams dom
      let img ← toYatimaExpr levelParams img
      return .pi nam bndInfo dom img
    | .letE nam typ exp bod _ => do
      let typ ← toYatimaExpr levelParams typ
      let exp ← toYatimaExpr levelParams exp
      let bod ← toYatimaExpr levelParams bod
      return .letE nam typ exp bod
    | .lit lit _ => return Yatima.Expr.lit lit
    | .mdata _ e _ => toYatimaExpr levelParams e
    | .proj .. => sorry
    | .fvar .. => sorry
    | .mvar .. => sorry

  partial def toYatimaConst : Lean.ConstantInfo → EnvM Const
    | .axiomInfo struct => do
      let env ← get
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid := type.toCid
      set { env with exprs := env.exprs.insert typeCid type }
      return .axiom {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        safe := not struct.isUnsafe }
    | .thmInfo struct => do
      let env ← get
      let type  ← toYatimaExpr struct.levelParams struct.type
      let typeCid  := type.toCid
      set { env with exprs := env.exprs.insert typeCid type }
      let value ← toYatimaExpr struct.levelParams struct.value
      let valueCid := value.toCid
      set { env with exprs := env.exprs.insert valueCid value }
      return .theorem {
        name  := struct.name
        lvls  := struct.levelParams.map .ofLeanName
        type  := typeCid
        value := valueCid }
    | .opaqueInfo struct => do
      let env ← get
      let type  ← toYatimaExpr struct.levelParams struct.type
      let typeCid  := type.toCid
      set { env with exprs := env.exprs.insert typeCid type }
      let value ← toYatimaExpr struct.levelParams struct.value
      let valueCid := value.toCid
      return .opaque {
        name  := struct.name
        lvls  := struct.levelParams.map .ofLeanName
        type  := typeCid
        value := valueCid
        safe  := not struct.isUnsafe }
    | .defnInfo struct => do
      let env ← get
      let type  ← toYatimaExpr struct.levelParams struct.type
      let typeCid  := type.toCid
      set { env with exprs := env.exprs.insert typeCid type }
      let value ← toYatimaExpr struct.levelParams struct.value
      let valueCid := value.toCid
      return .definition {
        name   := struct.name
        lvls   := struct.levelParams.map .ofLeanName
        type   := typeCid
        value  := valueCid
        safety := struct.safety }
    | .ctorInfo struct => do
      let env ← get
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid := type.toCid
      set { env with exprs := env.exprs.insert typeCid type }
      let ctorCid : ConstCid := sorry
      return .constructor {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        ind  := ctorCid
        idx  := struct.cidx
        params := struct.numParams
        fields := struct.numFields
        safe := not struct.isUnsafe }
    | .inductInfo struct => do
      let env ← get
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid := type.toCid
      set { env with exprs := env.exprs.insert typeCid type }
      return .inductive {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        params := struct.numParams
        indices := struct.numIndices
        ctors := struct.ctors.map .ofLeanName
        recr := struct.isRec
        refl := struct.isReflexive
        nest := struct.isNested
        safe := not struct.isUnsafe }
    | .recInfo struct => do
      let env ← get
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid := type.toCid
      set { env with exprs := env.exprs.insert typeCid type }
      let ctorCid : ConstCid := sorry
      return .recursor {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        params := struct.numParams
        ind := ctorCid
        motives := struct.numMotives
        indices := struct.numIndices
        minors := struct.numMinors
        rules := ← struct.rules.mapM $ toYatimaRecursorRule ctorCid
        k := struct.k
        safe := not struct.isUnsafe }
    | .quotInfo struct => do
      let env ← get
      let type ← toYatimaExpr struct.levelParams struct.type
      let typeCid := type.toCid
      set { env with exprs := env.exprs.insert typeCid type }
      return .quotient {
        name := struct.name
        lvls := struct.levelParams.map .ofLeanName
        type := typeCid
        kind := struct.kind }

end

def EnvM.run (constMap : Lean.ConstMap) (state : Env) (m : EnvM α) :
    Except String (α × Env) :=
  match EStateM.run (ReaderT.run m constMap) state with
  | .ok v env  => .ok (v, env)
  | .error e _ => .error e


def extractEnv (constMap : Lean.ConstMap) : Except String Env :=
  sorry

end Yatima.Compiler.FromLean
