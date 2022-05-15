use crate::{
  nat::Nat,
  typechecker::universe::*,
  typechecker::expression::*,
};
use im::Vector;
use std::rc::Rc;
use std::cell::RefCell;

// Expressions are things to be evaluated. Values are the result of evaluating (reducing, normalizing) expressions. However, in general, expressions
// need to be given an environment to give values to their free variables. So, from now on, when we write "unevaluated expression", we mean an expression
// plus an environment
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct UnExpr {
  expr: ExprPtr,
  // The environment will bind free variables to different things, depending on the evaluation strategy.
  // 1) Strict evaluation: binds free variables to values
  // 2) Non-strict evaluation: binds free variables to unevaluated expressions
  // 3) Lazy evaluation (i.e. non-strict without duplication of work): binds free variables to thunks
  // Here we chose lazy evaluation since it is more efficient for typechecking.
  fvar: Vector<ThunkPtr>,
  // Since we also have universes with free parameters, we need to add an environment for universe params as well:
  uvar: Vector<UnivPtr>,
}

// Thunks are either values or unevaluated expressions. Whenever we "force" a thunk (i.e. evaluate it in case it is not yet a value), we should update
// it to the result of the evaluation, so that we don't duplicate work evaluating it again
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Thunk {
  Res(Value),
  Sus(UnExpr),
}
pub type ThunkPtr = Rc<RefCell<Thunk>>;

// The arguments of a stuck sequence of applications `(h a1 ... an)`
pub type Args = Vector<ThunkPtr>;

/// Yatima values. We assume that values are only reduced from well-typed expressions.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Value {
  /// Type universes. It is assumed `Univ` is reduced/simplified
  Sort(Univ),
  /// Values can only be an application if its a stuck application. That is, if the head of the application is either a variable
  /// or a constant with not enough arguments to reduce (i.e. neutral terms)
  App(Neutral, Args),
  /// Lambdas are yet to be reduced expressions with environments for their free variables apart from their argument variables
  Lam(BinderInfo, UnExpr),
  /// Pi types will have thunks for their domains and an expression/environment pair analogous to a lambda for their images
  Pi(BinderInfo, ThunkPtr, UnExpr),
  /// Literal: "foo", 1, 2, 3
  Lit(Literal),
  /// Literal Type: Nat, String
  Lty(LitType),
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Neutral {
  FVar(Nat, ThunkPtr),
  Const(ConstPtr),
}
