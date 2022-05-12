import Lean
import Yatima.Ipld.Cid
import Yatima.Univ

inductive LitType where
  | natTyp
  | strTyp
  deriving Inhabited, BEq

mutual

  inductive YExpr
  | var   : Nat → YExpr
  | sort  : Univ → YExpr
  | const : YConst → List Univ → YExpr
  | app   : YExpr → YExpr → YExpr
  | lam   : YExpr → YExpr → YExpr
  | pi    : YExpr → YExpr → YExpr
  | letE  : YExpr → YExpr → YExpr → YExpr
  | lit   : Lean.Literal → YExpr
  | lty   : LitType → YExpr
  | fix   : YExpr → YExpr
  deriving Inhabited

  inductive YRecursorRule
  -- ctor, n_fields, rhs
  | mk : Cid → Nat → YExpr → YRecursorRule

  inductive YConst
  -- cid, level, type
  | axiomC : Cid → Nat → YExpr → YConst

  -- level, value, type
  | theoremC : Nat → YExpr → YExpr → YConst

  -- cid, level, value, type, is_unsafe
  | opaque : Cid → Nat → YExpr → YExpr → Bool → YConst

  -- cid, level, value, type, safety
  | defn : Cid → Nat → YExpr → YExpr → Lean.DefinitionSafety → YConst

  -- cid, level, type, ctor_idx, num_params, num_fields, is_unsafe
  | ctor : Cid → Nat → YExpr → Nat → Nat → Nat → Bool → YConst

  -- cid, level, type, num_params, num_indices, is_unit, is_rec, is_unsafe, is_reflexive, is_nested
  | induct : Cid → Nat → YExpr → Nat → Nat → Bool → Bool → Bool → Bool → Bool → YConst

  -- cid, level, type, num_params, num_indices, num_motives, num_minors, rules, k, is_unsafe
  | recursor : Cid → Nat → YExpr → Nat → Nat → Nat → Nat → List YRecursorRule → Bool → Bool → YConst

  -- level, type, kind
  | quotient : Nat → YExpr → Lean.QuotKind → YConst

end

instance : Inhabited YRecursorRule where
  default := YRecursorRule.mk default default default

instance : Inhabited YConst where
  default := YConst.axiomC default default default

-- def YConst.extractType : YConst → YExpr
--   | axiomC   x => x.type
--   | theoremC x => x.type
--   | opaque   x => x.type
--   | defn     x => x.type
--   | induct   x => x.type
--   | ctor     x => x.type
--   | recursor x => x.type
--   | quotient x => x.type
