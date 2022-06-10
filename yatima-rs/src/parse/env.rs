use alloc::string::{
  String,
  ToString,
};
use im::{
  OrdMap,
  Vector,
};
use libipld::Cid;
use num_traits::Zero;

use core::cell::{
  RefCell,
  RefMut,
};

use core::ops::DerefMut;

use crate::{
  constant::{
    Const,
    DefSafety,
    QuotKind,
  },
  environment::{
    ConstAnonCid,
    ConstCid,
    ConstMetaCid,
    Env,
    EnvError,
    ExprCid,
    CONST_ANON,
    CONST_META,
  },
  expression::{
    BinderInfo,
    Expr,
    LitType,
    Literal,
  },
  name::Name,
  nat::Nat,
  parse::{
    constant::parse_const,
    base::parse_multibase,
    error::{
      throw_err,
      ParseError,
      ParseErrorKind,
    },
    expr::parse_bound_expression,
    span::Span,
    string::parse_string,
    univ::parse_univ,
    utils::{
      parse_builtin_symbol_end,
      parse_name,
      parse_nat,
      parse_space,
      parse_space1,
      parse_u8,
      store_const,
      BindCtx,
      EnvCtx,
      GlobalCtx,
      UnivCtx,
    },
  },
  universe::Univ,
};
use nom::{
  branch::alt,
  bytes::complete::{
    tag,
    take_till,
    take_till1,
  },
  character::complete::{
    digit1,
    multispace0,
    multispace1,
    satisfy,
  },
  combinator::{
    eof,
    map,
    opt,
    peek,
    success,
    value,
  },
  error::context,
  multi::{
    many0,
    many1,
    separated_list1,
  },
  sequence::{
    delimited,
    preceded,
    terminated,
  },
  Err,
  IResult,
};

use super::expr::{
  parse_binders0,
  parse_expr,
  parse_expr_apps,
};

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
