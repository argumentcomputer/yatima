import Lean
import Yatima.Ipld.Cid
import Yatima.Univ

inductive LitType where
  | natTyp
  | strTyp
  deriving Inhabited, BEq

-- Lean does not support mutual blocks with structure and inductive, so we have to parametrize
-- the following structure
structure AxiomC (YExpr : Type) where
  cid : Cid
  level : Nat
  type : YExpr

structure TheoremC (YExpr : Type) where
  level : Nat
  expr : YExpr
  type : YExpr

structure OpaqueC (YExpr : Type) where
  cid : Cid
  level : Nat
  expr : YExpr
  type : YExpr
  is_unsafe : Bool

structure DefinitionC (YExpr : Type) where
  cid : Cid
  level : Nat
  expr : YExpr
  type : YExpr
  safety : Lean.DefinitionSafety

structure ConstructorC (YExpr : Type) where
  cid : Cid
  level : Nat
  type : YExpr
  ctor_idx : Nat
  num_params : Nat
  num_fields : Nat
  is_unsafe : Bool

structure InductiveC (YExpr : Type) where
  cid : Cid
  level : Nat
  type : YExpr
  num_params : Nat
  num_indices : Nat
  is_unit : Bool
  is_rec : Bool
  is_unsafe : Bool
  is_reflexive : Bool
  is_nested : Bool

structure RecursorRule (YExpr : Type) where
  ctor : Cid
  nfields : Nat
  rhs : YExpr
  deriving Inhabited

structure RecursorC (YExpr : Type) where
  cid : Cid
  level : Nat
  type : YExpr
  num_params : Nat
  num_indices : Nat
  num_motives : Nat
  num_minors : Nat
  rules : List (RecursorRule YExpr)
  k : Bool
  is_unsafe : Bool

structure QuotientC (YExpr : Type) where
  level : Nat
  type : YExpr
  kind : Lean.QuotKind

mutual
  inductive Const where
  | axiomC   : AxiomC YExpr → Const
  | theoremC : TheoremC YExpr → Const
  | opaque   : OpaqueC YExpr → Const
  | defn     : DefinitionC YExpr → Const
  | induct   : InductiveC YExpr → Const
  | ctor     : ConstructorC YExpr → Const
  | recursor : RecursorC YExpr → Const
  | quotient : QuotientC YExpr → Const

  inductive YExpr where
  | var   : Nat → YExpr
  | sort  : Univ → YExpr
  | const : Const → List Univ → YExpr
  | app   : YExpr → YExpr → YExpr
  | lam   : YExpr → YExpr → YExpr
  | pi    : YExpr → YExpr → YExpr
  | letE  : YExpr → YExpr → YExpr → YExpr
  | lit   : Lean.Literal → YExpr
  | lty   : LitType → YExpr
  | fix   : YExpr → YExpr
  deriving Inhabited
end

instance : Inhabited Const where
  default := Const.theoremC (TheoremC.mk 0 default default)

def extractConstType : Const → YExpr
  | Const.axiomC   x => x.type
  | Const.theoremC x => x.type
  | Const.opaque   x => x.type
  | Const.defn     x => x.type
  | Const.induct   x => x.type
  | Const.ctor     x => x.type
  | Const.recursor x => x.type
  | Const.quotient x => x.type
