use crate::{
  name::Name,
  nat::Nat,
  typechecker::universe::*,
};

use alloc::string::String;
use std::{
  collections::HashMap,
  rc::Rc,
};

pub type ExprPtr = Rc<Expr>;
pub type ConstPtr = Rc<Const>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Literal {
  Nat(Nat),
  Str(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitType {
  Nat,
  Str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinderInfo {
  Default,
  Implicit,
  StrictImplict,
  InstImplict,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefSafety {
  Unsafe,
  Safe,
  Partial,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuotKind {
  Type,
  Ctor,
  Lift,
  Ind,
}

/// Nameless expressions for typechecking. Such expressions must come from
/// ExprAnon in such a way that it preserves CID <-> Pointer correspondence.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Expr {
  /// Variables
  Var(Index),
  /// Type Universes
  Sort(UnivPtr),
  /// Global references to a Constant, with universe arguments
  Const(ConstPtr, Vec<UnivPtr>),
  /// Function Application: (f x)
  App(ExprPtr, ExprPtr),
  /// Anonymous Function: λ (x : A) => x
  Lam(BinderInfo, ExprPtr, ExprPtr),
  /// Universal Quantification: Π (x : A) -> x
  Pi(BinderInfo, ExprPtr, ExprPtr),
  /// Local definition: let x : A = e in b
  Let(ExprPtr, ExprPtr, ExprPtr),
  /// Literal: "foo", 1, 2, 3
  Lit(Literal),
  /// Literal Type: Nat, String
  Lty(LitType),
  /// Fixpoint recursion, μ x. x
  Fix(ExprPtr),
}

/// Constants for typechecking. They must also come from their anon
/// representation, preserving CID <-> correspondence
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Const {
  /// axiom
  Axiom { name: Name, uvars: Nat, typ: ExprPtr },
  /// theorem
  Theorem { uvars: Nat, typ: ExprPtr, expr: ExprPtr },
  /// opaque
  Opaque { name: Name, uvars: Nat, typ: ExprPtr, expr: ExprPtr, safe: bool },
  /// def
  Definition { uvars: Nat, typ: ExprPtr, expr: ExprPtr, safe: DefSafety },
  /// inductive type
  Inductive {
    uvars: Nat,
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
    uvars: Nat,
    ind: ConstPtr,
    typ: ExprPtr,
    idx: Nat,
    param: Nat,
    field: Nat,
    safe: bool,
  },
  /// inductive recursor
  Recursor {
    uvars: Nat,
    ind: ConstPtr,
    typ: ExprPtr,
    params: Index,
    indices: Index,
    motives: Index,
    minors: Index,
    /// Since pointers are in one-to-one correspondence with CIDs, we can use
    /// raw pointers as keys
    rules: HashMap<*const Const, RecursorRule>,
    k: bool,
    safe: bool,
  },
  /// quotient
  Quotient { kind: QuotKind },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursorRule {
  pub nfields: Index,
  pub rhs: ExprPtr,
}
