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
pub mod parse;
pub mod typechecker;
pub mod universe;

#[cfg(test)]
pub mod test {
  use quickcheck::{
    Arbitrary,
    Gen,
  };
  use rand::Rng;

  pub fn frequency<T, F: Fn(&mut Gen) -> T>(
    g: &mut Gen,
    gens: Vec<(i64, F)>,
  ) -> T {
    if gens.iter().any(|(v, _)| *v < 0) {
      panic!("Negative weight");
    }
    let sum: i64 = gens.iter().map(|x| x.0).sum();
    let mut rng = rand::thread_rng();
    let mut weight: i64 = rng.gen_range(1..=sum);
    // let mut weight: i64 = g.rng.gen_range(1, sum);
    for gen in gens {
      if weight - gen.0 <= 0 {
        return gen.1(g);
      }
      else {
        weight -= gen.0;
      }
    }
    panic!("Calculation error for weight = {}", weight);
  }
}
