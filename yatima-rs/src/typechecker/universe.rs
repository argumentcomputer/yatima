use crate::{
  nat::Nat,
};

pub type UnivPtr = u32;
pub type UnivStore = Vec<Univ>;

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
  Param(Nat),
}
