use crate::{
  name::Name,
  nat::Nat,
  universe::Univ,
};

use serde::{
  Deserialize,
  Serialize,
};

use alloc::{
  string::String,
};

pub type ExprPtr = u32;
pub type ExprStore = Vec<Expr>;
pub type ConstPtr = u32;
pub type ConstStore = Vec<Expr>;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Literal {
  Nat(Nat),
  Str(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LitType {
  Nat,
  Str,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinderInfo {
  Default,
  Implicit,
  StrictImplict,
  InstImplict,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum DefSafety {
  Unsafe,
  Safe,
  Partial,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum QuotKind {
  Type,
  Ctor,
  Lift,
  Ind,
}

/// Yatima Constants
#[derive(Clone, Debug)]
pub enum Const {
  /// axiom
  Axiom { name: Name, lvl: Vec<Name>, typ: ExprPtr },
  /// theorem
  Theorem { name: Name, lvl: Vec<Name>, typ: ExprPtr, expr: ExprPtr },
  /// opaque
  Opaque {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprPtr,
    expr: ExprPtr,
    safe: bool,
  },
  /// def
  Definition {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprPtr,
    expr: ExprPtr,
    safe: DefSafety,
  },
  /// inductive type
  Inductive {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprPtr,
    params: Nat,
    indices: Nat,
    unit: bool,
    rec: bool,
    safe: bool,
    refl: bool,
    nested: bool,
  },
  /// inductive constructor
  Constructor {
    name: Name,
    lvl: Vec<Name>,
    ind: ConstPtr,
    typ: ExprPtr,
    idx: Nat,
    param: Nat,
    field: Nat,
    safe: bool,
  },
  /// inductive recursor
  Recursor {
    lvl: Vec<Name>,
    ind: ConstPtr,
    typ: ExprPtr,
    params: Nat,
    indices: Nat,
    motives: Nat,
    minors: Nat,
    rules: Vec<(ConstPtr, Nat, Expr)>,
    k: bool,
    safe: bool,
  },
  /// quotient
  Quotient { kind: QuotKind },
}

/// Yatima Expressions
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Expr {
  /// Variables
  Var(Name, Nat),
  /// Type Universes
  Sort(Univ),
  /// Global references to a Constant, with universe arguments
  Const(Name, ConstPtr, Vec<Univ>),
  /// Function Application: (f x)
  App(ExprPtr, ExprPtr),
  /// Anonymous Function: λ (x : A) => x
  Lam(Name, BinderInfo, ExprPtr, ExprPtr),
  /// Universal Quantification: Π (x : A) -> x
  Pi(Name, BinderInfo, ExprPtr, ExprPtr),
  /// Local definition: let x : A = e in b
  Let(Name, ExprPtr, ExprPtr, ExprPtr),
  /// Literal: "foo", 1, 2, 3
  Lit(Literal),
  /// Literal Type: Nat, String
  Lty(LitType),
  /// Fixpoint recursion, μ x. x
  Fix(Name, ExprPtr),
}
