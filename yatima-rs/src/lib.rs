#![cfg_attr(test, feature(new_uninit))]
#![cfg_attr(test, feature(box_into_inner))]

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[cfg(test)]
extern crate rand;

extern crate alloc;

pub mod constant;
pub mod environment;
pub mod expression;
pub mod name;
pub mod nat;
// pub mod parse;
pub mod universe;
pub mod typechecker;
