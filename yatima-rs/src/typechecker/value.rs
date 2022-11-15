use crate::expression::{
    BinderInfo,
    Literal,
    LitType,
  };
use crate::typechecker::{
  expression::*,
  universe::*,
};
use im::Vector;
use std::{
  cell::RefCell,
  rc::Rc,
};

// Expressions are things to be evaluated, given an appropriate environment.
// Values are the result of evaluating (reducing, normalizing) expressions in an
// environment. Finally, environments are maps that gives free variables of
// expressions their values. When we talk about "unevaluated expressions",
// you should think of these expression/environment pairs
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Env {
  // The environment will bind free variables to different things, depending on
  // the evaluation strategy. 1) Strict evaluation: binds free variables to
  // values 2) Non-strict evaluation: binds free variables to unevaluated
  // expressions 3) Lazy evaluation (i.e. non-strict without duplication of
  // work): binds free variables to thunks Here we chose lazy evaluation
  // since it is more efficient for typechecking.
  pub exprs: Vector<ThunkPtr>,
  // Since we also have universes with free variables, we need to add an
  // environment for universe variables as well:
  pub univs: Vector<UnivPtr>,
}

// Thunks are either values or unevaluated expressions. Whenever we "force" a
// thunk (i.e. evaluate it in case it is not yet a value), we should update
// it to the result of the evaluation, so that we don't duplicate work
// evaluating it again
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Thunk {
  Res(Value),
  Sus(ExprPtr, Env),
}
// A thunk must be inside `RefCell` so we can have shared mutation
pub type ThunkPtr = Rc<RefCell<Thunk>>;

// The arguments of a stuck sequence of applications `(h a1 ... an)`
pub type Args = Vector<ThunkPtr>;

/// Yatima values. We assume that values are only reduced from well-typed
/// expressions.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Value {
  /// Type universes. It is assumed `Univ` is reduced/simplified
  Sort(UnivPtr),
  /// Values can only be an application if its a stuck application. That is, if
  /// the head of the application is either a variable or a constant with not
  /// enough arguments to reduce (i.e. neutral terms)
  App(Neutral, Args),
  /// Lambdas are unevaluated expressions with environments for their free
  /// variables apart from their argument variables
  Lam(BinderInfo, ExprPtr, Env),
  /// Pi types will have thunks for their domains and unevaluated expressions
  /// analogous to lambda bodies for their codomains
  Pi(BinderInfo, ThunkPtr, ExprPtr, Env),
  /// Literal: "foo", 1, 2, 3
  Lit(Literal),
  /// Literal Type: Nat, String
  Lty(LitType),
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Neutral {
  FVar(Index),
  Const(ConstPtr, Vector<UnivPtr>),
}
