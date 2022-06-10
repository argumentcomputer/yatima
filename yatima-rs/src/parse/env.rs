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

/// Parses each constant, storing them in the provided environment context.
pub fn parse_env(
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, (), ParseError<Span>> {
  move |i: Span| {
    let mut global_ctx = global_ctx.clone();
    let mut i = i.clone();
    loop {
      (i, _) = parse_space(i)?;
      match &parse_const(global_ctx.clone(), env_ctx.clone())(i) {
        Ok((_, cnst)) => {
          let res = store_const(env_ctx.clone(), cnst.clone(), i)?;
          i = res.0;
          global_ctx.insert(cnst.name(), res.1);
        },
        Err(_) => break Ok((i, ()))
      }
    }
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;

  use alloc::rc::Rc;

  use crate::expression::tests::dummy_global_ctx;

  use crate::environment::Env;
  use core::cell::RefCell;

  #[quickcheck]
  fn prop_env_parse_print(x: Env) -> bool {
    let s = x.pretty(false).unwrap();
    println!("input: \t\t{s}");
    let y = Rc::new(RefCell::new(Env::new()));
    let res = parse_env(dummy_global_ctx(), y.clone())(Span::new(&s));
    match res {
      Ok((_, _)) => {
        let y =  y.try_borrow().unwrap().clone();
        println!("re-parsed: \t{}", y.pretty(false).unwrap());
        x == y
      }
      Err(e) => {
        println!("err: {:?}", e);
        false
      }
    }
  }
}
