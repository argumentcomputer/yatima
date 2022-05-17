use crate::{
  typechecker::universe::*,
  typechecker::expression::*,
};
use im::Vector;
use std::rc::Rc;
use std::cell::RefCell;

// Expressions are things to be evaluated, given an appropriate environment. Values are the result of evaluating (reducing, normalizing) expressions in
// an environment. Finally, environments are maps that gives free variables of expressions their values. Since expressions and environments so often
// appear together, we'll bundle them up in a single struct. Such a struct represents a frozen computation, that can be run (evaluated).
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Comp {
  pub expr: ExprPtr,
  // The environment will bind free variables to different things, depending on the evaluation strategy.
  // 1) Strict evaluation: binds free variables to values
  // 2) Non-strict evaluation: binds free variables to computations
  // 3) Lazy evaluation (i.e. non-strict without duplication of work): binds free variables to thunks
  // Here we chose lazy evaluation since it is more efficient for typechecking.
  pub e_env: Vector<ThunkPtr>,
  // Since we also have universes with free variables, we need to add an environment for universe variables as well:
  pub u_env: Vector<UnivPtr>,
}

// Thunks are either values or frozen computations. Whenever we "force" a thunk (i.e. evaluate it in case it is not yet a value), we should update
// it to the result of the evaluation, so that we don't duplicate work evaluating it again
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Thunk {
  Res(Value),
  Sus(Comp),
}
// A thunk must be inside `RefCell` so we can have shared mutation
pub type ThunkPtr = Rc<RefCell<Thunk>>;

// The arguments of a stuck sequence of applications `(h a1 ... an)`
pub type Args = Vector<ThunkPtr>;

/// Yatima values. We assume that values are only reduced from well-typed expressions.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Value {
  /// Type universes. It is assumed `Univ` is reduced/simplified
  Sort(UnivPtr),
  /// Values can only be an application if its a stuck application. That is, if the head of the application is either a variable
  /// or a constant with not enough arguments to reduce (i.e. neutral terms)
  App(Neutral, Args),
  /// Lambdas are frozen computations with environments for their free variables apart from their argument variables
  Lam(BinderInfo, Comp),
  /// Pi types will have thunks for their domains and frozen computations analogous to lambda bodies for their codomains
  Pi(BinderInfo, ThunkPtr, Comp),
  /// Literal: "foo", 1, 2, 3
  Lit(Literal),
  /// Literal Type: Nat, String
  Lty(LitType),
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Neutral {
  // Free variables also carry around their types for efficiency
  FVar(Index, ThunkPtr),
  Const(ConstPtr, Vector<UnivPtr>),
}
