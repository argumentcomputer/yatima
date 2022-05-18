import Yatima.Ipld.Keccak
import Yatima.Ipld.Cid
import Yatima.Expr
import Yatima.Univ
import Yatima.Env
import Yatima.Cid
import Yatima.Const

import Lean

namespace Lean.Yatima.Compiler

instance : Inhabited Yatima.Const where
  default := Yatima.Const.axiom ⟨default, default, default, default⟩

instance : Coe Name Yatima.Name where
  coe := Yatima.Name.ofLeanName

instance : Coe DefinitionSafety Yatima.DefinitionSafety where coe
  | .safe      => .safe
  | .«unsafe»  => .«unsafe»
  | .«partial» => .«partial»

instance : Coe BinderInfo Yatima.BinderInfo where coe
  | .default        => .default
  | .auxDecl        => .auxDecl
  | .instImplicit   => .instImplicit
  | .strictImplicit => .strictImplicit
  | .implicit       => .implicit

instance : Coe QuotKind Yatima.QuotKind where coe
  | .type => .type
  | .ind  => .ind
  | .lift => .lift
  | .ctor => .ctor

instance : Coe Literal Yatima.Literal where coe
  | .natVal n => .nat n
  | .strVal s => .str s

def toYatimaLevel (levelParams : List Name) : Level → Except String Yatima.Univ
  | .zero _      => .ok .zero
  | .succ n _    => match toYatimaLevel levelParams n with
    | .ok u         => .ok $ .succ u
    | e@(.error ..) => e
  | .max  a b _  =>
    match (toYatimaLevel levelParams a), (toYatimaLevel levelParams b) with
    | .ok u, .ok u'    => .ok $ .max u u'
    | e@(.error ..), _ => e
    | _, e@(.error ..) => e
  | .imax a b _  =>
    match (toYatimaLevel levelParams a), (toYatimaLevel levelParams b) with
    | .ok u, .ok u'    => .ok $ .imax u u'
    | e@(.error ..), _ => e
    | _, e@(.error ..) => e
  | .param nam _ => match levelParams.indexOf nam with
    | some n => .ok $ .param nam n
    | none   => .error s!"'{nam}' not found in '{levelParams}'"
  | .mvar .. => .error "Unfilled level metavariable"

mutual

 partial def toYatimaRecursorRule (constMap : ConstMap) (rules : RecursorRule) :
     Except String Yatima.RecRule := do
   let rhs ← toYatimaExpr constMap [] rules.rhs
   return Yatima.RecRule.mk sorry rules.nfields rhs

  partial def toYatimaConst (constMap : ConstMap) : ConstantInfo → Except String Yatima.Const
    | .axiomInfo struct =>
      return Yatima.Const.axiom {
        name := struct.name
        lvls := struct.levelParams.map Yatima.Name.ofLeanName
        type := ← toYatimaExpr constMap struct.levelParams struct.type
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

  partial def toYatimaExpr (constMap : ConstMap) (levelParams : List Name) :
      Expr → Except String Yatima.Expr
    | .bvar idx _ => return .var "" idx
    | .sort lvl _ =>
      match toYatimaLevel levelParams lvl with
      | .ok u    => .ok $ .sort u
      | .error s => .error s
    | .const nam lvls _ => do
      match constMap.find?' nam with
      | some const => do
        let mut consts := []
        let mut failure : Option String := none
        for x in lvls.map $ toYatimaLevel levelParams do
          match x with
          | .ok    c => consts  := c :: consts -- faster, but reversed
          | .error s => failure := some s; break
        match failure with
        | none   => .ok $ .const nam sorry consts.reverse
        | some s => .error s
      | none => .error "Unknown constant"
    | .app fnc arg _ => do
      let fnc ← toYatimaExpr constMap levelParams fnc
      let arg ← toYatimaExpr constMap levelParams arg
      return .app fnc arg
    | .lam nam bnd bod _ => do
      let bndInfo := bnd.binderInfo
      let bnd ← toYatimaExpr constMap levelParams bnd
      let bod ← toYatimaExpr constMap levelParams bod
      return .lam nam bndInfo bnd bod
    | .forallE nam dom img _ => do
      let bndInfo := dom.binderInfo
      let dom ← toYatimaExpr constMap levelParams dom
      let img ← toYatimaExpr constMap levelParams img
      return .pi nam bndInfo dom img
    | .letE nam typ exp bod _ => do
      let typ ← toYatimaExpr constMap levelParams typ
      let exp ← toYatimaExpr constMap levelParams exp
      let bod ← toYatimaExpr constMap levelParams bod
      return .letE nam typ exp bod
    | .lit lit _ => return Yatima.Expr.lit lit
    | .mdata _ e _ => toYatimaExpr constMap levelParams e
    | .proj .. => panic! "Projections TODO"
    | .fvar .. => panic! "Unbound variable"
    | .mvar .. => panic! "Unfilled metavariable"

end
