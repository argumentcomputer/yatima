use crate::parse::{
  error::ParseError,
  span::Span,
  constant::parse_const,
  utils::{
    parse_space,
    store_const,
    EnvCtx,
    GlobalCtx,
  }
};

use nom::IResult;

/// Parses each constant, storing them in the provided environment context
/// and updating the given global context accordingly.
pub fn parse_env<'a, 'b>(
  global_ctx: &'b mut GlobalCtx,
  env_ctx: EnvCtx,
) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, (), ParseError<Span<'a>>> + 'b { 
  move |i: Span| {
    let mut i = i.clone();
    loop {
      (i, _) = parse_space(i)?;
      match &parse_const(global_ctx.clone(), env_ctx.clone())(i) {
        Ok((new_i, cnst)) => {
          i = *new_i;
          let res = store_const(env_ctx.clone(), cnst.clone(), i)?;
          i = res.0;
          global_ctx.insert(cnst.name(), res.1);
        },
        Err(_) => {
          break Ok((i, ()))
        }
      }
    }
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;

  use alloc::rc::Rc;

  use crate::environment::Env;
  use core::cell::RefCell;

  use im::OrdMap;

  #[quickcheck]
  fn prop_env_parse_print(x: Env) -> bool {
    let s = x.pretty(false).unwrap();
    println!("input: \n{s}");
    let y = Rc::new(RefCell::new(Env::new()));
    let res = parse_env(&mut OrdMap::new(), y.clone())(Span::new(&s));
    match res {
      Ok((_, _)) => {
        let y =  y.try_borrow().unwrap().clone();
        println!("re-parsed: \n{}", y.pretty(false).unwrap());
        if x != y { println!("ORIG: \t{:?}\nNEW: \t{:?}", x, y) }
        x == y
      }
      Err(e) => {
        println!("err: {:?}", e);
        false
      }
    }
  }
}
