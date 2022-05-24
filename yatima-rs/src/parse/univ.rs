use alloc::string::{
  String,
  ToString,
};
use im::Vector;

use crate::parse::{
  error::{
    ParseError,
    ParseErrorKind,
  },
  span::Span,
  utils::{
    parse_nat,
    parse_u8,
  },
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

use crate::{
  name::Name,
  nat::Nat,
  universe::Univ,
};

use super::utils::{
  parse_name,
  parse_space,
};

pub type UnivCtx = Vector<Name>;

pub fn parse_univ_constant()
-> impl Fn(Span) -> IResult<Span, Univ, ParseError<Span>> {
  move |from: Span| {
    // TODO: Is there a better way to protect against unary number bombs than
    // making u8::MAX the largest universe we can use this syntax for?
    let (i, mut nat) = parse_u8(from)?;
    let mut univ = Univ::Zero;
    while nat > 0u8 {
      univ = Univ::Succ(Box::new(univ));
      nat = nat - 1u8;
    }
    Ok((i, univ))
  }
}

pub fn parse_univ_param(
  ctx: UnivCtx,
) -> impl Fn(Span) -> IResult<Span, Univ, ParseError<Span>> {
  move |from: Span| {
    let (upto, nam) = parse_name(from)?;
    if let Some((idx, _)) = ctx.iter().enumerate().find(|(_, x)| **x == nam) {
      Ok((upto, Univ::Param(nam.clone(), idx.into())))
    }
    else {
      Err(Err::Error(ParseError::new(
        upto,
        ParseErrorKind::UndefinedUniverse(nam.clone(), ctx.clone()),
      )))
    }
  }
}

pub fn parse_univ_add(
  ctx: UnivCtx,
) -> impl Fn(Span) -> IResult<Span, Univ, ParseError<Span>> {
  move |from: Span| {
    let (i, mut univ) = parse_univ(ctx.clone())(from)?;
    let (i, _) = parse_space(i)?;
    let (i, _) = tag("+")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, mut nat) = parse_u8(i)?;
    while nat > 0u8 {
      univ = Univ::Succ(Box::new(univ));
      nat = nat - 1u8;
    }
    Ok((i, univ))
  }
}

pub fn parse_univ_max(
  ctx: UnivCtx,
) -> impl Fn(Span) -> IResult<Span, Univ, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = tag("max")(from)?;
    let (i, _) = parse_space(i)?;
    let (i, l) = parse_univ(ctx.clone())(i)?;
    let (i, _) = parse_space(i)?;
    let (i, r) = parse_univ(ctx.clone())(i)?;
    Ok((i, Univ::Max(Box::new(l), Box::new(r))))
  }
}

pub fn parse_univ_imax(
  ctx: UnivCtx,
) -> impl Fn(Span) -> IResult<Span, Univ, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = tag("imax")(from)?;
    let (i, _) = parse_space(i)?;
    let (i, l) = parse_univ(ctx.clone())(i)?;
    let (i, _) = parse_space(i)?;
    let (i, r) = parse_univ(ctx.clone())(i)?;
    Ok((i, Univ::IMax(Box::new(l), Box::new(r))))
  }
}

pub fn parse_univ(
  ctx: UnivCtx,
) -> impl Fn(Span) -> IResult<Span, Univ, ParseError<Span>> {
  move |from: Span| {
    alt((
      delimited(
        preceded(tag("("), parse_space),
        parse_univ_imax(ctx.clone()),
        preceded(parse_space, tag(")")),
      ),
      delimited(
        preceded(tag("("), parse_space),
        parse_univ_max(ctx.clone()),
        preceded(parse_space, tag(")")),
      ),
      delimited(
        preceded(tag("("), parse_space),
        parse_univ_add(ctx.clone()),
        preceded(parse_space, tag(")")),
      ),
      parse_univ_constant(),
      parse_univ_param(ctx.clone()),
    ))(from)
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;

  #[test]
  fn test_parse_univ_constant() {
    fn test(i: &str) -> IResult<Span, Univ, ParseError<Span>> {
      parse_univ(Vector::new())(Span::new(i))
    }
    let res = test("0");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Univ::Zero);
    let res = test("1");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Univ::Succ(Box::new(Univ::Zero)));
    let res = test("255");
    assert!(res.is_ok());
    let res = test("256");
    assert!(res.is_err());
  }

  #[test]
  fn test_parse_univ_param() {
    fn test(ctx: Vec<Name>, i: &str) -> IResult<Span, Univ, ParseError<Span>> {
      parse_univ(ctx.into())(Span::new(i))
    }
    let res = test(vec!["x".into()], "x");
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Univ::Param("x".into(), 0u8.into()));
    let res = test(vec!["y".into(), "x".into()], "x");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Univ::Param("x".into(), 1u8.into()));
    let res = test(vec!["y".into(), "x".into()], "y");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Univ::Param("y".into(), 0u8.into()));
  }

  #[test]
  fn test_parse_univ_max() {
    fn test(ctx: Vec<Name>, i: &str) -> IResult<Span, Univ, ParseError<Span>> {
      parse_univ(ctx.into())(Span::new(i))
    }
    let res = test(vec!["x".into()], "(max x x)");
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Univ::Max(
        Box::new(Univ::Param("x".into(), 0u8.into())),
        Box::new(Univ::Param("x".into(), 0u8.into()))
      )
    );
    let res = test(vec!["y".into(), "x".into()], "(max (max x y) 1)");
    assert!(res.is_ok());
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Univ::Max(
        Box::new(Univ::Max(
          Box::new(Univ::Param("x".into(), 1u8.into())),
          Box::new(Univ::Param("y".into(), 0u8.into()))
        )),
        Box::new(Univ::Succ(Box::new(Univ::Zero)))
      )
    );
  }

  #[test]
  fn test_parse_univ_imax() {
    fn test(ctx: Vec<Name>, i: &str) -> IResult<Span, Univ, ParseError<Span>> {
      parse_univ(ctx.into())(Span::new(i))
    }
    let res = test(vec!["x".into()], "(imax x x)");
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Univ::IMax(
        Box::new(Univ::Param("x".into(), 0u8.into())),
        Box::new(Univ::Param("x".into(), 0u8.into()))
      )
    );
    let res = test(vec!["y".into(), "x".into()], "(imax (imax x y) 1)");
    assert!(res.is_ok());
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Univ::IMax(
        Box::new(Univ::IMax(
          Box::new(Univ::Param("x".into(), 1u8.into())),
          Box::new(Univ::Param("y".into(), 0u8.into()))
        )),
        Box::new(Univ::Succ(Box::new(Univ::Zero)))
      )
    );
  }

  #[test]
  fn test_parse_univ_add() {
    fn test(ctx: Vec<Name>, i: &str) -> IResult<Span, Univ, ParseError<Span>> {
      parse_univ(ctx.into())(Span::new(i))
    }
    let res = test(vec!["x".into()], "(x + 1)");
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Univ::Succ(Box::new(Univ::Param("x".into(), 0u8.into())))
    );
    let res = test(vec!["y".into(), "x".into()], "((x + 1) + 1)");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Univ::Succ(Box::new(Univ::Succ(Box::new(Univ::Param(
        "x".into(),
        1u8.into()
      ))))),
    );
  }
}
