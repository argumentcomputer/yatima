import Yatima.Ipld.Keccak
import Yatima.Ipld.Cid
import Yatima.Expr
import Yatima.Univ
import Yatima.Env
import Yatima.Cid
import Yatima.Const

import Lean

namespace Lean.Yatima.Compiler

instance : Coe Name Yatima.Name where
  coe := Yatima.Name.ofLeanName

instance : Inhabited Yatima.Const where
  default := Yatima.Const.axiom ⟨Yatima.Name.anon, [], default, default⟩

instance : Coe DefinitionSafety Yatima.DefSafety where
  coe := fun ds => match ds with
    | .safe      => .safe
    | .«unsafe»  => .«unsafe»
    | .«partial» => .«partial»

instance : Coe QuotKind Yatima.QuotKind where
  coe := fun q => match q with
    | .type => .type
    | .ind  => .ind
    | .lift => .lift
    | .ctor => .ctor

instance : Coe Literal Yatima.Literal where
  coe := fun l => match l with
    | .natVal n => .nat n
    | .strVal s => .str s

abbrev ConstMap := SMap Name Yatima.Const

structure Context where
  env      : Lean.Environment
  constMap : Lean.ConstMap := {}

abbrev ConvM := ReaderT Context $ StateT ConstMap Id

instance : Monad ConvM :=
  let i := inferInstanceAs (Monad ConvM)
  { pure := i.pure, bind := i.bind }

--todo As it stands, it is using Keccak256. Should be parametrized on hash functions later
def nameToCid (nam : Name) : Cid :=
  -- Should we use `Name.hash` or our own encoding of names?
  let digest  := Keccak.keccak256 $ ByteArray.pushUInt64LE ByteArray.empty nam.hash
  let size    := sorry
  let code    := sorry
  let version := sorry
  let codec   := sorry
  let multihash := Multihash.mk size code digest
  Cid.mk version codec multihash

def leanExprToCid (e : Expr) : Cid := panic! "TODO"
def combineCid (a : Cid) (b : Cid) : Cid := panic! "TODO"

def inductiveIsUnitLike (ctors : List Name) : ConvM Bool :=
  match ctors with
  | [ctor] => do
    match Environment.find? (← read).env ctor with
    | some info =>
      match info with
      | ConstantInfo.ctorInfo cval => pure (cval.numFields != 0)
      | _ => pure false
    | none => pure false
  | _ => pure false

def toYatimaLevel (levelParams : List Name) : Level → Yatima.Univ
  | .zero _      => Yatima.Univ.zero
  | .succ n _    => Yatima.Univ.succ (toYatimaLevel levelParams n)
  | .max  a b _  => Yatima.Univ.max  (toYatimaLevel levelParams a) (toYatimaLevel levelParams b)
  | .imax a b _  => Yatima.Univ.imax (toYatimaLevel levelParams a) (toYatimaLevel levelParams b)
  | .param nam _ =>
    match levelParams.indexOf nam with
    | some n => Yatima.Univ.param nam n
    | none   => panic! s!"'{nam}' not found in '{levelParams}'"
  | .mvar _ _ => panic! "Unfilled level metavariable"

mutual

 partial def toYatimaRecursorRule (rules : RecursorRule) :
     ConvM Yatima.RecRule := do
   let cid := sorry
   let rhs ← toYatimaExpr [] rules.rhs
   return Yatima.RecRule.mk cid rules.nfields rhs

 partial def toYatimaConstMap (nam : Name) : ConvM ConstMap := do
   let insertConst := fun nam const => do
     let _ ← toYatimaConst nam const
     pure default
   SMap.forM (← read).constMap insertConst
   get

  partial def toYatimaConst (nam : Name) (constInfo : ConstantInfo) :
      ConvM Yatima.Const := do
    let YatimaMap ← get
    match YatimaMap.find?' nam with
    | some const => pure const
    | none => do
      let const ← match constInfo with
      | .axiomInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        pure $ Yatima.Const.axiom {
          name := struct.name
          lvls := struct.levelParams.map Yatima.Name.ofLeanName
          type := ← toYatimaExpr struct.levelParams struct.type
          safe := not struct.isUnsafe }
      | .thmInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        pure $ Yatima.Const.theorem {
          name  := struct.name
          lvls  := struct.levelParams.map Yatima.Name.ofLeanName
          type  := ← toYatimaExpr struct.levelParams struct.type
          value := ← toYatimaExpr struct.levelParams struct.value }
      | .opaqueInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        pure $ Yatima.Const.opaque {
          name  := struct.name
          lvls  := struct.levelParams.map Yatima.Name.ofLeanName
          type  := ← toYatimaExpr struct.levelParams struct.type
          value := ← toYatimaExpr struct.levelParams struct.value
          safe  := not struct.isUnsafe }
      | .defnInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        pure $ Yatima.Const.definition {
          name  := struct.name
          lvls  := struct.levelParams.map Yatima.Name.ofLeanName
          type  := ← toYatimaExpr struct.levelParams struct.type
          value := ← toYatimaExpr struct.levelParams struct.value
          safe  := struct.safety }
      | .ctorInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        pure $ Yatima.Const.constructor {
          name := struct.name
          lvls := struct.levelParams.map Yatima.Name.ofLeanName
          type := ← toYatimaExpr struct.levelParams struct.type
          ind  := sorry
          idx  := struct.cidx
          params := struct.numParams
          fields := struct.numFields
          safe := not struct.isUnsafe }
      | .inductInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        pure $ Yatima.Const.inductive {
          name := struct.name
          lvls := struct.levelParams.map Yatima.Name.ofLeanName
          type := ← toYatimaExpr struct.levelParams struct.type
          params := struct.numParams
          indices := struct.numIndices
          ctors := struct.ctors.map Yatima.Name.ofLeanName
          recr := struct.isRec
          refl := struct.isReflexive
          nest := struct.isNested
          safe := not struct.isUnsafe }
      | .recInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        pure $ Yatima.Const.recursor {
          name := struct.name
          lvls := struct.levelParams.map Yatima.Name.ofLeanName
          type := ← toYatimaExpr struct.levelParams struct.type
          params := struct.numParams
          ind := sorry
          motives := struct.numMotives
          indices := struct.numIndices
          minors := struct.numMinors
          rules := ← struct.rules.mapM toYatimaRecursorRule
          k := struct.k
          safe := not struct.isUnsafe }
      | .quotInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        pure $ Yatima.Const.quotient {
          name := struct.name
          lvls := struct.levelParams.map Yatima.Name.ofLeanName
          type := ← toYatimaExpr struct.levelParams struct.type
          kind := struct.kind }
      modifyGet fun YatimaMap => (const, SMap.insert' YatimaMap nam const)

  partial def toYatimaExpr (levelParams : List Name) : Expr → ConvM Yatima.Expr
    | .bvar idx _ => return Yatima.Expr.var .anon idx
    | .sort lvl _ => return Yatima.Expr.sort (toYatimaLevel levelParams lvl)
    | .const nam lvls _ => do
      match (← read).constMap.find?' nam with
      | some const =>
        let const ← toYatimaConst nam const
        return Yatima.Expr.const nam
          sorry
          (lvls.map $ toYatimaLevel levelParams)
      | none => panic! "Unknown constant"
    | .app fnc arg _ => do
      let fnc ← toYatimaExpr levelParams fnc
      let arg ← toYatimaExpr levelParams arg
      return Yatima.Expr.app fnc arg
    | .lam nam bnd bod _ => do
      let bndInfo := bnd.binderInfo
      let bnd ← toYatimaExpr levelParams bnd
      let bod ← toYatimaExpr levelParams bod
      return Yatima.Expr.lam nam bndInfo bnd bod
    | .forallE nam dom img _ => do
      let bndInfo := dom.binderInfo
      let dom ← toYatimaExpr levelParams dom
      let img ← toYatimaExpr levelParams img
      return Yatima.Expr.pi nam bndInfo dom img
    | .letE nam typ exp bod _ => do
      let typ ← toYatimaExpr levelParams typ
      let exp ← toYatimaExpr levelParams exp
      let bod ← toYatimaExpr levelParams bod
      return Yatima.Expr.letE nam typ exp bod
    | .lit lit _ => return Yatima.Expr.lit lit
    | .mdata _ e _ => toYatimaExpr levelParams e
    | .proj .. => panic! "Projections TODO"
    | .fvar .. => panic! "Unbound variable"
    | .mvar .. => panic! "Unfilled metavariable"

end
