use alloc::string::{
  String,
  ToString,
};
use im::{
  OrdMap,
  Vector,
};
use libipld::Cid;

use crate::{
  environment::{
    ConstAnonCid,
    ConstCid,
    ConstMetaCid,
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
    base::parse_multibase,
    error::{
      throw_err,
      ParseError,
      ParseErrorKind,
    },
    span::Span,
    string::parse_string,
    univ::{
      parse_univ,
      UnivCtx,
    },
    utils::{
      parse_builtin_symbol_end,
      parse_name,
      parse_nat,
      parse_space,
      parse_u8,
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

pub type BindCtx = Vector<Name>;
pub type GlobalCtx = OrdMap<Name, ConstCid>;

pub fn parse_expr_var(
  bind_ctx: BindCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (upto, nam) = parse_name(from)?;
    if let Some((idx, _)) =
      bind_ctx.iter().enumerate().find(|(_, x)| **x == nam)
    {
      Ok((upto, Expr::Var(nam.clone(), idx.into())))
    }
    else {
      Err(Err::Error(ParseError::new(
        upto,
        ParseErrorKind::UndefinedReference(nam.clone(), bind_ctx.clone()),
      )))
    }
  }
}

pub fn parse_cid(from: Span) -> IResult<Span, Cid, ParseError<Span>> {
  let (upto, (_, bytes)) = parse_multibase()(from)?;
  match Cid::try_from(bytes) {
    Ok(cid) => Ok((upto, cid)),
    Err(_) => Err(Err::Error(ParseError::new(upto, ParseErrorKind::CidError))),
  }
}

//// `bafyqwoieruwqoieruuoqweqwerq.bafyqwoieruwqoieruuoqweqwerq
pub fn parse_const_cid(
  from: Span,
) -> IResult<Span, ConstCid, ParseError<Span>> {
  let (i, anon) = parse_cid(from)?;
  let (i, _) = tag(".")(i)?;
  let (i, meta) = parse_cid(i)?;
  if anon.codec() == CONST_ANON && meta.codec() == CONST_META {
    Ok((i, ConstCid { anon: ConstAnonCid(anon), meta: ConstMetaCid(meta) }))
  }
  else {
    Err(Err::Error(ParseError::new(i, ParseErrorKind::CidError)))
  }
}
pub fn parse_univ_args(
  univ_ctx: UnivCtx,
) -> impl Fn(Span) -> IResult<Span, Vec<Univ>, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = tag("{")(from)?;
    let (i, args) =
      many0(preceded(parse_space, parse_univ(univ_ctx.clone())))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, _) = tag("}")(i)?;
    Ok((i, args))
  }
}

// `foo:bafyqwoieruwqoieruuoqweqwerqw.bafyqwoieruwqoieruuoqweqwerq {u v w}`
pub fn parse_expr_const(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i, nam) = parse_name(from)?;
    let (i, cid) = opt(preceded(tag(":"), parse_const_cid))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, args) = parse_univ_args(univ_ctx.clone())(i)?;
    if let Some(cid) = cid {
      Ok((i, Expr::Const(nam, cid, args)))
    }
    else if let Some(cid) = global_ctx.get(&nam) {
      Ok((i, Expr::Const(nam, *cid, args)))
    }
    else {
      Err(Err::Error(ParseError::new(
        i,
        ParseErrorKind::UndefinedReference(nam.clone(), bind_ctx.clone()),
      )))
    }
  }
}

/// Parses a literal type
pub fn parse_expr_lty() -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>>
{
  move |from: Span| {
    let (i, lty) = alt((
      value(LitType::Nat, tag("#Nat")),
      value(LitType::Str, tag("#Str")),
    ))(from)?;
    let (upto, _) = throw_err(parse_builtin_symbol_end()(i), |_| {
      ParseError::new(
        i,
        ParseErrorKind::LitTypeLacksTermination(lty.to_owned()),
      )
    })?;
    Ok((upto, Expr::Lty(lty)))
  }
}

pub fn parse_lit_str(from: Span) -> IResult<Span, Literal, ParseError<Span>> {
  let (i, _) = context("open quotes", tag("\""))(from)?;
  let (i, s) = parse_string("\"")(i)?;
  let (upto, _) = tag("\"")(i)?;
  Ok((upto, Literal::Str(s.into())))
}
pub fn parse_lit_nat(from: Span) -> IResult<Span, Literal, ParseError<Span>> {
  let (i, n) = parse_nat(from)?;
  Ok((i, Literal::Nat(n)))
}

/// Parses a literal
pub fn parse_expr_lit() -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>>
{
  move |from: Span| {
    let (i, lit) = alt((parse_lit_str, parse_lit_nat))(from)?;
    let (i, _) = throw_err(parse_builtin_symbol_end()(i), |_| {
      ParseError::new(
        i,
        ParseErrorKind::LiteralLacksTermination(lit.to_owned()),
      )
    })?;
    Ok((i, Expr::Lit(lit)))
  }
}

pub fn parse_expr_sort(
  univ_ctx: UnivCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = tag("Sort")(from)?;
    let (i, _) = parse_space(i)?;
    let (i, u) = parse_univ(univ_ctx.clone())(i)?;
    Ok((i, Expr::Sort(u)))
  }
}

/// Parse the termination marker of an application sequence
pub fn parse_app_end(i: Span) -> IResult<Span, (), ParseError<Span>> {
  let (i, _) = alt((
    peek(tag("def")),
    peek(tag("inductive")),
    peek(tag("axiom")),
    peek(tag("theorem")),
    peek(tag(":=")),
    peek(tag("->")),
    peek(tag("in")),
    peek(tag(")")),
    peek(tag("{")),
    peek(tag("}")),
    peek(tag("[")),
    peek(tag("]")),
    peek(tag(",")),
    peek(eof),
  ))(i)?;
  Ok((i, ()))
}

/// Parse an application sequence `f a b c`
pub fn parse_expr_apps(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i2, _) = parse_space(from)?;
    let (i2, fun) =
      parse_expr(univ_ctx.clone(), bind_ctx.clone(), global_ctx.clone())(i2)?;
    let mut i = i2;
    let mut args = Vec::new();
    loop {
      let (i2, _) = parse_space(i)?;
      match parse_app_end(i2) {
        Ok((..)) => {
          let trm = args
            .into_iter()
            .fold(fun, |acc, arg| Expr::App(Box::new(acc), Box::new(arg)));
          return Ok((i2, trm));
        }
        _ => {
          let (i2, arg) =
            parse_expr(univ_ctx.clone(), bind_ctx.clone(), global_ctx.clone())(
              i2,
            )?;
          args.push(arg);
          i = i2
        }
      }
    }
  }
}

/// Parse a binder
pub fn parse_binder(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
) -> impl Fn(Span) -> IResult<Span, (BinderInfo, Name, Expr), ParseError<Span>>
{
  move |i: Span| {
    let (i, bind) = alt((
      value(BinderInfo::Default, tag("(")),
      value(BinderInfo::StrictImplict, tag("{{")),
      value(BinderInfo::Implicit, tag("{")),
      value(BinderInfo::InstImplict, tag("[")),
    ))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, nam) = parse_name(i)?;
    let (i, _) = parse_space(i)?;
    let (i, _) = tag(":")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, typ) =
      parse_expr_apps(univ_ctx.clone(), bind_ctx.clone(), global_ctx.clone())(
        i,
      )?;
    let close = match bind {
      BinderInfo::Default => ")",
      BinderInfo::StrictImplict => "}}",
      BinderInfo::Implicit => "}",
      BinderInfo::InstImplict => "]",
    };
    let (i, _) = tag(close)(i)?;
    Ok((i, (bind, nam, typ)))
  }
}

/// Parse zero or more binders
pub fn parse_binders0(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  terminator: Vec<char>,
) -> impl FnMut(Span) -> IResult<Span, Vec<(BinderInfo, Name, Expr)>, ParseError<Span>>
{
  move |mut i: Span| {
    let mut bind_ctx = bind_ctx.clone();
    let mut res = Vec::new();

    loop {
      match preceded(parse_space, peek(satisfy(|x| terminator.contains(&x))))(i)
      {
        Ok((i2, _)) => return Ok((i2, res)),
        _ => {}
      }
      match preceded(
        parse_space,
        parse_binder(univ_ctx.clone(), bind_ctx.clone(), global_ctx.clone()),
      )(i)
      {
        Err(e) => return Err(e),
        Ok((i2, (b, n, t))) => {
          bind_ctx.push_front(n.to_owned());
          res.push((b, n, t));
          i = i2;
        }
      }
    }
  }
}

pub fn parse_binders1(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  terminator: Vec<char>,
) -> impl FnMut(Span) -> IResult<Span, Vec<(BinderInfo, Name, Expr)>, ParseError<Span>>
{
  move |mut i: Span| {
    let mut bind_ctx = bind_ctx.clone();
    let mut res = Vec::new();

    match preceded(
      parse_space,
      parse_binder(univ_ctx.clone(), bind_ctx.clone(), global_ctx.clone()),
    )(i)
    {
      Err(e) => return Err(e),
      Ok((i2, (b, n, t))) => {
        bind_ctx.push_front(n.to_owned());
        res.push((b, n, t));
        i = i2;
      }
    }
    let (i, mut res2) = parse_binders0(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      terminator.clone(),
    )(i)?;
    res.append(&mut res2);
    Ok((i, res))
  }
}

pub fn parse_expr_lam(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = alt((tag("λ"), tag("lambda")))(from)?;
    let (i, _) = parse_space(i)?;
    let (i, bs) = parse_binders1(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      vec!['='],
    )(i)?;
    let (i, _) = tag("=>")(i)?;
    let (i, _) = parse_space(i)?;
    let mut body_bind_ctx = bind_ctx.clone();
    for (_, n, _) in bs.clone().iter() {
      body_bind_ctx.push_front(n.clone());
    }
    let (upto, bod) = parse_expr_apps(
      univ_ctx.clone(),
      body_bind_ctx.clone(),
      global_ctx.clone(),
    )(i)?;
    let trm = bs
      .into_iter()
      .rev()
      .fold(bod, |acc, (b, n, t)| Expr::Lam(n, b, Box::new(t), Box::new(acc)));
    Ok((upto, trm))
  }
}

pub fn parse_expr_pi(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = alt((tag("∀"), tag("forall")))(from)?;
    let (i, _) = parse_space(i)?;
    let (i, bs) = parse_binders1(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      vec!['-'],
    )(i)?;
    let (i, _) = tag("->")(i)?;
    let (i, _) = parse_space(i)?;
    let mut body_bind_ctx = bind_ctx.clone();
    for (_, n, _) in bs.clone().iter() {
      body_bind_ctx.push_front(n.clone());
    }
    let (upto, bod) = parse_expr_apps(
      univ_ctx.clone(),
      body_bind_ctx.clone(),
      global_ctx.clone(),
    )(i)?;
    let trm = bs
      .into_iter()
      .rev()
      .fold(bod, |acc, (b, n, t)| Expr::Lam(n, b, Box::new(t), Box::new(acc)));
    Ok((upto, trm))
  }
}

/// The input `(A: Type) (x: A) : A = x` returns:
///   - type: `∀ (A: Type) (x: A) -> A`
///   - term: `λ A x => x`
/// This is useful for parsing lets and defs
pub fn parse_bound_expression(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
) -> impl Fn(Span) -> IResult<Span, (Expr, Expr), ParseError<Span>> {
  move |from: Span| {
    let (i, bs) = parse_binders0(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      vec![':'],
    )(from)?;
    let (i, _) = tag(":")(i)?;
    let (i, _) = parse_space(i)?;
    let mut type_bind_ctx = bind_ctx.clone();
    for (_, n, _) in bs.iter() {
      type_bind_ctx.push_front(n.clone());
    }
    let (i, typ) = parse_expr_apps(
      univ_ctx.clone(),
      type_bind_ctx.clone(),
      global_ctx.clone(),
    )(i)?;
    let mut term_bind_ctx = bind_ctx.clone();
    for (_, n, _) in bs.iter() {
      term_bind_ctx.push_front(n.clone());
    }
    let (i, _) = parse_space(i)?;
    let (i, _) = tag(":=")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, trm) = parse_expr_apps(
      univ_ctx.clone(),
      type_bind_ctx.clone(),
      global_ctx.clone(),
    )(i)?;
    let trm = bs.iter().rev().fold(trm, |acc, (b, n, t)| {
      Expr::Lam(n.clone(), b.clone(), Box::new(t.clone()), Box::new(acc))
    });
    let typ = bs
      .into_iter()
      .rev()
      .fold(typ, |acc, (b, n, t)| Expr::Pi(n, b, Box::new(t), Box::new(acc)));
    Ok((i, (typ, trm)))
  }
}

/// Parses a local function definition
pub fn parse_let(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = tag("let")(from)?;
    let (i, _) = parse_space(i)?;
    let (i, nam) = parse_name(i)?;
    let (i, _) = parse_space(i)?;
    let (i, (typ, exp)) = parse_bound_expression(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
    )(i)?;
    let (i, _) = alt((tag(";"), tag("in")))(i)?;
    let (i, _) = parse_space(i)?;
    let mut body_bind_ctx = bind_ctx.clone();
    body_bind_ctx.push_front(nam.clone());
    let (upto, bod) = parse_expr_apps(
      univ_ctx.clone(),
      body_bind_ctx.clone(),
      global_ctx.clone(),
    )(i)?;
    Ok((upto, Expr::Let(nam, Box::new(typ), Box::new(exp), Box::new(bod))))
  }
}

/// Parses each term variant
pub fn parse_expr(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |i: Span| {
    alt((
      delimited(
        tag("("),
        parse_expr_apps(univ_ctx.clone(), bind_ctx.clone(), global_ctx.clone()),
        tag(")"),
      ),
      parse_expr_lam(univ_ctx.clone(), bind_ctx.clone(), global_ctx.clone()),
      parse_expr_pi(univ_ctx.clone(), bind_ctx.clone(), global_ctx.clone()),
      parse_expr_lit(),
      parse_expr_lty(),
      parse_expr_sort(univ_ctx.clone()),
      parse_expr_const(univ_ctx.clone(), bind_ctx.clone(), global_ctx.clone()),
      parse_expr_var(bind_ctx.clone()),
    ))(i)
  }
}

#[cfg(test)]
pub mod tests {
  use crate::constant::ConstAnon;
  use multihash::{
    Code,
    MultihashDigest,
  };

  use super::*;

  #[test]
  fn test_parse_lit() {
    fn test(i: &str) -> IResult<Span, Expr, ParseError<Span>> {
      parse_expr(Vector::new(), Vector::new(), OrdMap::new())(Span::new(i))
    }
    let res = test("1");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Lit(Literal::Nat(1u64.into())));
    let res = test("\"foo\"");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Lit(Literal::Str("foo".into())));
  }

  #[test]
  fn test_parse_var() {
    fn test<'a>(
      ctx: Vec<&str>,
      i: &'a str,
    ) -> IResult<Span<'a>, Expr, ParseError<Span<'a>>> {
      let ctx: Vec<Name> = ctx.into_iter().map(|x| x.into()).collect();
      parse_expr(Vector::new(), ctx.into(), OrdMap::new())(Span::new(i))
    }
    let res = test(vec!["x", "y", "z"], "x");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Var("x".into(), 0u64.into()));
    let res = test(vec!["x", "y", "z"], "y");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Var("y".into(), 1u64.into()));
    let res = test(vec!["x", "y", "z"], "a");
    assert!(res.is_err());
    let res = test(vec!["x", "y", "z", "x"], "x");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Var("x".into(), 0u64.into()))
  }

  #[test]
  fn test_parse_sort() {
    fn test<'a>(
      ctx: Vec<&str>,
      i: &'a str,
    ) -> IResult<Span<'a>, Expr, ParseError<Span<'a>>> {
      let ctx: Vec<Name> = ctx.into_iter().map(|x| x.into()).collect();
      parse_expr(ctx.into(), Vector::new(), OrdMap::new())(Span::new(i))
    }
    let res = test(vec!["u", "v", "w"], "Sort u");
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Sort(Univ::Param("u".into(), 0u64.into()))
    );
    let res = test(vec!["u", "v", "w"], "Sort w");
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Sort(Univ::Param("w".into(), 2u64.into()))
    );
    let res = test(vec!["u", "v", "w"], "Sort 0");
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Sort(Univ::Zero));
  }

  fn dummy_const_cid() -> ConstCid {
    let anon: ConstAnonCid = ConstAnonCid::new(Code::Sha3_256.digest(&[0]));
    let meta: ConstMetaCid = ConstMetaCid::new(Code::Sha3_256.digest(&[0]));
    ConstCid { anon, meta }
  }

  fn dummy_global_ctx() -> GlobalCtx {
    OrdMap::from(vec![(Name::from("foo"), dummy_const_cid())])
  }

  #[test]
  fn test_parse_const() {
    fn test<'a>(
      univ_ctx: Vec<&str>,
      bind_ctx: Vec<&str>,
      i: &'a str,
    ) -> IResult<Span<'a>, Expr, ParseError<Span<'a>>> {
      let univ_ctx: Vec<Name> =
        univ_ctx.into_iter().map(|x| x.into()).collect();
      let bind_ctx: Vec<Name> =
        bind_ctx.into_iter().map(|x| x.into()).collect();
      parse_expr(univ_ctx.into(), bind_ctx.into(), dummy_global_ctx())(
        Span::new(i),
      )
    }
    let res = test(vec![], vec![], "foo {}");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Const("foo".into(), dummy_const_cid(), vec![])
    );
    let res = test(vec![], vec!["foo"], "foo {}");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Const("foo".into(), dummy_const_cid(), vec![])
    );
    let res = test(vec!["u", "v"], vec![], "foo {u v}");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Const("foo".into(), dummy_const_cid(), vec![
        Univ::Param("u".into(), 0u64.into()),
        Univ::Param("v".into(), 1u64.into())
      ])
    );
    let res = test(
      vec![],
      vec![],
      "foo:bagbyb6egbqlcaxkti2psb7xu7dvlkk4iarhn42ohpjvgrjqhfbqj7rfgl72tdz6q.\
       bagdib6egbqlcaxkti2psb7xu7dvlkk4iarhn42ohpjvgrjqhfbqj7rfgl72tdz6q {}",
    );
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Const("foo".into(), dummy_const_cid(), vec![])
    );
  }
  #[test]
  fn test_parse_apps() {
    fn test<'a>(
      ctx: Vec<&str>,
      i: &'a str,
    ) -> IResult<Span<'a>, Expr, ParseError<Span<'a>>> {
      let ctx: Vec<Name> = ctx.into_iter().map(|x| x.into()).collect();
      parse_expr_apps(Vector::new(), ctx.into(), OrdMap::new())(Span::new(i))
    }
    let res = test(vec!["x", "y"], "x y");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::App(
        Box::new(Expr::Var("x".into(), 0u64.into())),
        Box::new(Expr::Var("y".into(), 1u64.into()))
      )
    );
    let res = test(vec!["x", "y", "z"], "x y z");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::App(
        Box::new(Expr::App(
          Box::new(Expr::Var("x".into(), 0u64.into())),
          Box::new(Expr::Var("y".into(), 1u64.into()))
        )),
        Box::new(Expr::Var("z".into(), 2u64.into()))
      )
    );
  }

  #[test]
  fn test_parse_pi() {
    fn test(i: &str) -> IResult<Span, Expr, ParseError<Span>> {
      parse_expr(Vector::new(), Vector::new(), OrdMap::new())(Span::new(i))
    }
    let res = test("∀ (a: Sort 0) -> Sort 0");
    assert!(res.is_ok());
    let res = test("∀ (A: Sort 0) (x : A) -> A");
    println!("{:?}", res);
    assert!(res.is_ok());
  }
  #[test]
  fn test_parse_lam() {
    fn test(i: &str) -> IResult<Span, Expr, ParseError<Span>> {
      parse_expr(Vector::new(), Vector::new(), OrdMap::new())(Span::new(i))
    }
    let res = test("λ (a: Sort 0) => Sort 0");
    assert!(res.is_ok());
    let res = test("λ (A: Sort 0) (x : A) => A");
    assert!(res.is_ok());
    let res = test("λ [X: Sort 0] {X: Sort 0} (A: Sort 0) (x : A) => A");
    println!("{:?}", res);
    assert!(res.is_ok());
  }
}
