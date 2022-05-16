use std::rc::Rc;

pub type UnivPtr = Rc<Univ>;
pub type EnvPtr = u32;

/// Universe levels
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Univ {
  /// Sort 0 aka Prop
  Zero,
  /// Sort (n + 1)
  Succ(UnivPtr),
  /// Sort (max u v)
  Max(UnivPtr, UnivPtr),
  /// Sort (imax u v)
  IMax(UnivPtr, UnivPtr),
  /// Sort u
  Var(EnvPtr),
}
