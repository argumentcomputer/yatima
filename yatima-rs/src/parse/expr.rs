use core::ops::DerefMut;

use libipld::Cid;
use num_traits::Zero;

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
    univ::parse_univ,
    utils::{
      parse_builtin_symbol_end,
      parse_name,
      parse_nat,
      parse_space,
      parse_space1,
      parse_u8,
      store_univ,
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

// `foo:bafyqwoieruwqoieruuoqweqwerqw.bafyqwoieruwqoieruuoqweqwerq.{u v w}`
pub fn parse_expr_const(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i, nam) = parse_name(from)?;
    let (i, cid) = opt(preceded(tag(":"), parse_const_cid))(i)?;
    let (i, args) = opt(preceded(tag("."), parse_univ_args(univ_ctx.clone())))(i)?;
    let mut arg_cids = Vec::new();
    if let Some(args) = args {
      for arg in args {
        let (_, cid) = store_univ(env_ctx.clone(), arg, i)?;
        arg_cids.push(cid);
      }
    }
    if let Some(cid) = cid {
      Ok((i, Expr::Const(nam, cid, arg_cids)))
    }
    else if let Some(cid) = global_ctx.get(&nam) {
      Ok((i, Expr::Const(nam, *cid, arg_cids)))
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
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i, res) = opt(tag("Prop"))(from)?;
    if let Some(_) = res {
      let (i, cid) = store_univ(env_ctx.clone(), Univ::Zero, i)?;
      return Ok((i, Expr::Sort(cid)))
    }
    let (i, _) = tag("Sort")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, u) = parse_univ(univ_ctx.clone())(i)?;
    let (i, cid) = store_univ(env_ctx.clone(), u, i)?;
    Ok((i, Expr::Sort(cid)))
  }
}

/// Parse the termination marker of an application sequence
pub fn parse_app_end(i: Span) -> IResult<Span, (), ParseError<Span>> {
  let (i, _) = peek(
    alt((
      eof,
      tag(":="),
      tag("->"),
      tag("→"),
      tag(")"),
      tag("{"),
      tag("}"),
      tag("["),
      tag("]"),
      tag(","),
      preceded(
        alt((
          tag("def"),
          tag("inductive"),
          tag("axiom"),
          tag("theorem"),
          tag("opaque"),
          tag("unsafe"),
          tag("partial"),
          tag("where"),
          tag("in"),
        )),
        alt((
          eof,
          tag(" "),
          tag("\n"),
        ))
      )
    ))
  )(i)?;
  Ok((i, ()))
}

/// Parse an application sequence `f a b c`
pub fn parse_expr_apps(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i2, _) = parse_space(from)?;
    let (i2, fun) = parse_expr(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
    )(i2)?;
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
          let (i2, arg) = parse_expr(
            univ_ctx.clone(),
            bind_ctx.clone(),
            global_ctx.clone(),
            env_ctx.clone(),
          )(i2)?;
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
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Vec<(BinderInfo, Name, Expr)>, ParseError<Span>>
{
  move |i: Span| {
    let (i, bind) = alt((
      value(BinderInfo::Default, tag("(")),
      value(BinderInfo::StrictImplicit, tag("{{")),
      value(BinderInfo::Implicit, tag("{")),
      value(BinderInfo::InstImplicit, tag("[")),
    ))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, ns) = many1(terminated(parse_name, parse_space))(i)?;
    let (i, _) = tag(":")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, typ) = parse_expr_apps(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
    )(i)?;
    let close = match bind {
      BinderInfo::Default => ")",
      BinderInfo::StrictImplicit => "}}",
      BinderInfo::Implicit => "}",
      BinderInfo::InstImplicit => "]",
    };
    let (i, _) = tag(close)(i)?;
    let mut res = Vec::new();
    for (i, n) in ns.iter().enumerate() {
      res.push((
        bind.clone(),
        n.to_owned(),
        typ.clone().shift(&Nat::from(i), &Some(Nat::zero())),
      ))
    }
    Ok((i, res))
  }
}

/// Parse zero or more binders
pub fn parse_binders0(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
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
        parse_binder(
          univ_ctx.clone(),
          bind_ctx.clone(),
          global_ctx.clone(),
          env_ctx.clone(),
        ),
      )(i)
      {
        Err(e) => return Err(e),
        Ok((i2, bs)) => {
          for (b, n, t) in bs {
            bind_ctx.push_front(n.to_owned());
            res.push((b, n, t));
          }
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
  env_ctx: EnvCtx,
  terminator: Vec<char>,
) -> impl FnMut(Span) -> IResult<Span, Vec<(BinderInfo, Name, Expr)>, ParseError<Span>>
{
  move |mut i: Span| {
    let mut bind_ctx = bind_ctx.clone();
    let mut res = Vec::new();

    match preceded(
      parse_space,
      parse_binder(
        univ_ctx.clone(),
        bind_ctx.clone(),
        global_ctx.clone(),
        env_ctx.clone(),
      ),
    )(i)
    {
      Err(e) => return Err(e),
      Ok((i2, bs)) => {
        for (b, n, t) in bs {
          bind_ctx.push_front(n.to_owned());
          res.push((b, n, t));
        }
        i = i2;
      }
    }
    let (i, mut res2) = parse_binders0(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
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
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = alt((tag("λ"), tag("lambda")))(from)?;
    let (i, _) = parse_space(i)?;
    let (i, bs) = parse_binders1(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
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
      env_ctx.clone(),
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
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = alt((tag("∀"), tag("Π"), tag("forall")))(from)?;
    let (i, _) = parse_space(i)?;
    let (i, bs) = parse_binders1(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
      vec!['-', '→'],
    )(i)?;
    let (i, _) = alt((tag("→"), tag("->")))(i)?;
    let (i, _) = parse_space(i)?;
    let mut body_bind_ctx = bind_ctx.clone();
    for (_, n, _) in bs.clone().iter() {
      body_bind_ctx.push_front(n.clone());
    }
    let (upto, bod) = parse_expr_apps(
      univ_ctx.clone(),
      body_bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
    )(i)?;
    let trm = bs
      .into_iter()
      .rev()
      .fold(bod, |acc, (b, n, t)| Expr::Pi(n, b, Box::new(t), Box::new(acc)));
    Ok((upto, trm))
  }
}

/// Parses an implixit fixpoint. This syntax is not exposed to the user in order
/// to avoid the creation of degenerate terms, such as `μ x . x`, which have no
/// semantic meaning. It is instead only used in `let rec` expression or
/// `def rec` constants
pub fn parse_rec_expr(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
  name: Option<Name>,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |i: Span| {
    if let Some(name) = &name {
      let mut bind_ctx = bind_ctx.clone();
      bind_ctx.push_front(name.clone());
      let (i, expr) = parse_expr(
        univ_ctx.clone(),
        bind_ctx.clone(),
        global_ctx.clone(),
        env_ctx.clone(),
      )(i)?;
      Ok((i, Expr::Fix(name.clone(), Box::new(expr))))
    }
    else {
      parse_expr(
        univ_ctx.clone(),
        bind_ctx.clone(),
        global_ctx.clone(),
        env_ctx.clone(),
      )(i)
    }
  }
}

pub fn parse_rec_expr_apps(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
  name: Option<Name>,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |i: Span| {
    if let Some(name) = &name {
      let mut bind_ctx = bind_ctx.clone();
      bind_ctx.push_front(name.clone());
      let (i, expr) = parse_expr_apps(
        univ_ctx.clone(),
        bind_ctx.clone(),
        global_ctx.clone(),
        env_ctx.clone(),
      )(i)?;
      Ok((i, Expr::Fix(name.clone(), Box::new(expr))))
    }
    else {
      parse_expr_apps(
        univ_ctx.clone(),
        bind_ctx.clone(),
        global_ctx.clone(),
        env_ctx.clone(),
      )(i)
    }
  }
}

/// The input `(A: Type) (x: A) : A := x` returns:
///   - type: `∀ (A: Type) (x: A) -> A`
///   - term: `λ A x => x`
/// This is useful for parsing lets and defs
pub fn parse_bound_expression(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
  rec: Option<Name>,
) -> impl Fn(Span) -> IResult<Span, (Expr, Expr), ParseError<Span>> {
  move |from: Span| {
    let (i, bs) = parse_binders0(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
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
      env_ctx.clone(),
    )(i)?;
    let mut term_bind_ctx = bind_ctx.clone();
    if let Some(name) = &rec {
      term_bind_ctx.push_front(name.clone());
    }
    for (_, n, _) in bs.iter() {
      term_bind_ctx.push_front(n.clone());
    }
    let (i, _) = parse_space(i)?;
    let (i, _) = tag(":=")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, trm) = parse_expr_apps(
      univ_ctx.clone(),
      term_bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
    )(i)?;
    let mut trm = bs.iter().rev().fold(trm, |acc, (b, n, t)| {
      Expr::Lam(n.clone(), b.clone(), Box::new(t.clone()), Box::new(acc))
    });
    if let Some(name) = &rec {
      trm = Expr::Fix(name.clone(), Box::new(trm));
    }
    let typ = bs
      .into_iter()
      .rev()
      .fold(typ, |acc, (b, n, t)| Expr::Pi(n, b, Box::new(t), Box::new(acc)));
    Ok((i, (typ, trm)))
  }
}

/// Parses a local function definition
pub fn parse_expr_let(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = tag("let")(from)?;
    let (i, _) = parse_space(i)?;
    let (i, rec) = opt(preceded(tag("rec"), parse_space1))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, nam) = parse_name(i)?;
    let rec = rec.map(|_| nam.clone());
    let (i, _) = parse_space(i)?;
    let (i, (typ, exp)) = parse_bound_expression(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
      rec,
    )(i)?;
    let (i, _) = alt((tag(";"), tag("in")))(i)?;
    let (i, _) = parse_space(i)?;
    let mut body_bind_ctx = bind_ctx.clone();
    body_bind_ctx.push_front(nam.clone());
    let (upto, bod) = parse_expr_apps(
      univ_ctx.clone(),
      body_bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
    )(i)?;
    Ok((upto, Expr::Let(nam, Box::new(typ), Box::new(exp), Box::new(bod))))
  }
}

/// Parses each term variant
pub fn parse_expr(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Expr, ParseError<Span>> {
  move |i: Span| {
    alt((
      delimited(
        tag("("),
        parse_expr_apps(
          univ_ctx.clone(),
          bind_ctx.clone(),
          global_ctx.clone(),
          env_ctx.clone(),
        ),
        tag(")"),
      ),
      parse_expr_lam(
        univ_ctx.clone(),
        bind_ctx.clone(),
        global_ctx.clone(),
        env_ctx.clone(),
      ),
      parse_expr_pi(
        univ_ctx.clone(),
        bind_ctx.clone(),
        global_ctx.clone(),
        env_ctx.clone(),
      ),
      parse_expr_lit(),
      parse_expr_lty(),
      parse_expr_sort(univ_ctx.clone(), env_ctx.clone()),
      parse_expr_let(
        univ_ctx.clone(),
        bind_ctx.clone(),
        global_ctx.clone(),
        env_ctx.clone(),
      ),
      parse_expr_const(
        univ_ctx.clone(),
        bind_ctx.clone(),
        global_ctx.clone(),
        env_ctx.clone(),
      ),
      parse_expr_var(bind_ctx.clone()),
    ))(i)
  }
}

#[cfg(test)]
pub mod tests {
  use alloc::rc::Rc;
  use core::cell::RefCell;
  use im::{
    OrdMap,
    Vector,
  };

  use crate::environment::Env;

  use crate::constant::ConstAnon;
  use multihash::{
    Code,
    MultihashDigest,
  };

  use crate::expression::tests::{dummy_univ_ctx, dummy_global_ctx, dummy_const_cid};

  use crate::expression::tests::ExprEnv;

  use rand::Rng;

  use super::*;

  #[test]
  fn test_parse_lit() {
    let env_ctx = Rc::new(RefCell::new(Env::new()));
    fn test(env_ctx: EnvCtx, i: &str) -> IResult<Span, Expr, ParseError<Span>> {
      parse_expr(Vector::new(), Vector::new(), OrdMap::new(), env_ctx)(
        Span::new(i),
      )
    }
    let res = test(env_ctx.clone(), "1");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Lit(Literal::Nat(1u64.into())));
    let res = test(env_ctx.clone(), "\"foo\"");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Lit(Literal::Str("foo".into())));
  }

  #[test]
  fn test_parse_var() {
    let env_ctx = Rc::new(RefCell::new(Env::new()));
    fn test<'a>(
      env_ctx: EnvCtx,
      ctx: Vec<&str>,
      i: &'a str,
    ) -> IResult<Span<'a>, Expr, ParseError<Span<'a>>> {
      let ctx: Vec<Name> = ctx.into_iter().map(|x| x.into()).collect();
      parse_expr(Vector::new(), ctx.into(), OrdMap::new(), env_ctx)(Span::new(
        i,
      ))
    }
    let res = test(env_ctx.clone(), vec!["x", "y", "z"], "x");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Var("x".into(), 0u64.into()));
    let res = test(env_ctx.clone(), vec!["x", "y", "z"], "y");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Var("y".into(), 1u64.into()));
    let res = test(env_ctx.clone(), vec!["x", "y", "z"], "a");
    assert!(res.is_err());
    let res = test(env_ctx.clone(), vec!["x", "y", "z", "x"], "x");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Expr::Var("x".into(), 0u64.into()))
  }

  #[test]
  fn test_parse_sort() {
    let env_ctx = Rc::new(RefCell::new(Env::new()));
    fn test<'a>(
      env_ctx: EnvCtx,
      ctx: Vec<&str>,
      i: &'a str,
    ) -> IResult<Span<'a>, Expr, ParseError<Span<'a>>> {
      let ctx: Vec<Name> = ctx.into_iter().map(|x| x.into()).collect();
      parse_expr(ctx.into(), Vector::new(), OrdMap::new(), env_ctx)(Span::new(
        i,
      ))
    }
    let res = test(env_ctx.clone(), vec!["u", "v", "w"], "Sort u");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Sort(
        Univ::Param("u".into(), 0u64.into()).cid(&mut Env::new()).unwrap()
      )
    );
    let res = test(env_ctx.clone(), vec!["u", "v", "w"], "Sort w");
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Sort(
        Univ::Param("w".into(), 2u64.into()).cid(&mut Env::new()).unwrap()
      )
    );
    let res = test(env_ctx.clone(), vec!["u", "v", "w"], "Sort 0");
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap())
    );
  }

  #[test]
  fn test_parse_const() {
    let env_ctx = Rc::new(RefCell::new(Env::new()));
    fn test<'a>(
      env_ctx: EnvCtx,
      univ_ctx: Vec<&str>,
      bind_ctx: Vec<&str>,
      i: &'a str,
    ) -> IResult<Span<'a>, Expr, ParseError<Span<'a>>> {
      let univ_ctx: Vec<Name> =
        univ_ctx.into_iter().map(|x| x.into()).collect();
      let bind_ctx: Vec<Name> =
        bind_ctx.into_iter().map(|x| x.into()).collect();
      parse_expr(univ_ctx.into(), bind_ctx.into(), dummy_global_ctx(), env_ctx)(
        Span::new(i),
      )
    }
    let res = test(env_ctx.clone(), vec![], vec![], "foo.{}");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Const("foo".into(), dummy_const_cid(0), vec![])
    );
    let res = test(env_ctx.clone(), vec![], vec![], "foo");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Const("foo".into(), dummy_const_cid(0), vec![])
    );
    let res = test(env_ctx.clone(), vec![], vec!["foo"], "foo.{}");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Const("foo".into(), dummy_const_cid(0), vec![])
    );
    let res = test(env_ctx.clone(), vec!["u", "v"], vec![], "foo.{u v}");
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Const("foo".into(), dummy_const_cid(0), vec![
        Univ::Param("u".into(), 0u64.into()).cid(&mut Env::new()).unwrap(),
        Univ::Param("v".into(), 1u64.into()).cid(&mut Env::new()).unwrap()
      ])
    );
    let res = test(
      env_ctx.clone(),
      vec![],
      vec![],
      "foo:bagbyb6egbqlcaxkti2psb7xu7dvlkk4iarhn42ohpjvgrjqhfbqj7rfgl72tdz6q.\
       bagdib6egbqlcaxkti2psb7xu7dvlkk4iarhn42ohpjvgrjqhfbqj7rfgl72tdz6q {}",
    );
    println!("{:?}", res);
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::Const("foo".into(), dummy_const_cid(0), vec![])
    );
  }
  #[test]
  fn test_parse_apps() {
    let env_ctx = Rc::new(RefCell::new(Env::new()));
    fn test<'a>(
      env_ctx: EnvCtx,
      ctx: Vec<&str>,
      i: &'a str,
    ) -> IResult<Span<'a>, Expr, ParseError<Span<'a>>> {
      let ctx: Vec<Name> = ctx.into_iter().map(|x| x.into()).collect();
      parse_expr_apps(Vector::new(), ctx.into(), OrdMap::new(), env_ctx)(
        Span::new(i),
      )
    }
    let res = test(env_ctx.clone(), vec!["x", "y"], "x y");
    assert!(res.is_ok());
    assert_eq!(
      res.unwrap().1,
      Expr::App(
        Box::new(Expr::Var("x".into(), 0u64.into())),
        Box::new(Expr::Var("y".into(), 1u64.into()))
      )
    );
    let res = test(env_ctx.clone(), vec!["x", "y", "z"], "x y z");
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
  fn test_parse_binder() {
    let env_ctx = Rc::new(RefCell::new(Env::new()));
    fn test<'a>(
      env_ctx: EnvCtx,
      ctx: Vec<&str>,
      i: &'a str,
    ) -> IResult<Span<'a>, Vec<(BinderInfo, Name, Expr)>, ParseError<Span<'a>>>
    {
      let ctx: Vec<Name> = ctx.into_iter().map(|x| x.into()).collect();
      parse_binder(Vector::new(), ctx.into(), OrdMap::new(), env_ctx)(
        Span::new(i),
      )
    }
    let res = test(env_ctx.clone(), vec![], "(a b c: Sort 0)");
    assert!(res.is_ok());
    let res = res.unwrap().1;
    assert_eq!(res, vec![
      (
        BinderInfo::Default,
        Name::from("a"),
        Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap())
      ),
      (
        BinderInfo::Default,
        Name::from("b"),
        Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap())
      ),
      (
        BinderInfo::Default,
        Name::from("c"),
        Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap())
      )
    ]);
    let res = test(env_ctx.clone(), vec!["A"], "(a b c: A)");
    assert!(res.is_ok());
    let res = res.unwrap().1;
    assert_eq!(res, vec![
      (
        BinderInfo::Default,
        Name::from("a"),
        Expr::Var(Name::from("A"), Nat::from(0 as usize))
      ),
      (
        BinderInfo::Default,
        Name::from("b"),
        Expr::Var(Name::from("A"), Nat::from(1 as usize))
      ),
      (
        BinderInfo::Default,
        Name::from("c"),
        Expr::Var(Name::from("A"), Nat::from(2 as usize))
      ),
    ]);
    let res = test(env_ctx.clone(), vec!["A"], "(a : ∀ (x: A) -> A)");
    assert!(res.is_ok());
    let res = res.unwrap().1;
    assert_eq!(res, vec![(
      BinderInfo::Default,
      Name::from("a"),
      Expr::Pi(
        Name::from("x"),
        BinderInfo::Default,
        Box::new(Expr::Var(Name::from("A"), Nat::from(0 as usize))),
        Box::new(Expr::Var(Name::from("A"), Nat::from(1 as usize)))
      )
    ),]);

    fn test_binders<'a>(
      env_ctx: EnvCtx,
      ctx: Vec<&str>,
      i: &'a str,
    ) -> IResult<Span<'a>, Vec<(BinderInfo, Name, Expr)>, ParseError<Span<'a>>>
    {
      let ctx: Vec<Name> = ctx.into_iter().map(|x| x.into()).collect();
      parse_binders0(Vector::new(), ctx.into(), OrdMap::new(), env_ctx, vec![
        ':',
      ])(Span::new(i))
    }
    let res1 = test(env_ctx.clone(), vec!["A"], "(a : ∀ (x: A) -> A)");
    let res2 = test_binders(env_ctx.clone(), vec!["A"], "(a : ∀ (x: A) -> A):");
    assert!(res1.is_ok() && res2.is_ok());
    let (res1, res2) = (res1.unwrap().1, res2.unwrap().1);
    assert_eq!(res1, res2);
    let res1 = test(env_ctx.clone(), vec!["A"], "(a b c: ∀ (x: A) -> A)");
    let res2 = test_binders(
      env_ctx.clone(),
      vec!["A"],
      "(a : ∀ (x: A) -> A)
       (b : ∀ (x: A) -> A)
       (c : ∀ (x: A) -> A)
    :",
    );
    assert!(res1.is_ok() && res2.is_ok());
    let (res1, res2) = (res1.unwrap().1, res2.unwrap().1);
    assert_eq!(res1, res2);
    let res1 =
      test(env_ctx.clone(), vec!["A"], "(a b c d e f g: ∀ (x y z w: A) -> A)");
    let res2 = test_binders(
      env_ctx.clone(),
      vec!["A"],
      "(a: ∀ (x y z w: A) -> A)
       (b: ∀ (x y z w: A) -> A)
       (c: ∀ (x y z w: A) -> A)
       (d: ∀ (x y z w: A) -> A)
       (e: ∀ (x y z w: A) -> A)
       (f: ∀ (x y z w: A) -> A)
       (g: ∀ (x y z w: A) -> A)
    :",
    );
    assert!(res1.is_ok() && res2.is_ok());
    let (res1, res2) = (res1.unwrap().1, res2.unwrap().1);
    assert_eq!(res1, res2);

    let res =
      test_binders(env_ctx.clone(), Vec::new(), "(A: Sort 0) (a b c: A):");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, vec![
      (
        BinderInfo::Default,
        Name::from("A"),
        Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap())
      ),
      (
        BinderInfo::Default,
        Name::from("a"),
        Expr::Var(Name::from("A"), Nat::from(0 as usize))
      ),
      (
        BinderInfo::Default,
        Name::from("b"),
        Expr::Var(Name::from("A"), Nat::from(1 as usize))
      ),
      (
        BinderInfo::Default,
        Name::from("c"),
        Expr::Var(Name::from("A"), Nat::from(2 as usize))
      ),
    ]);

    let res = test_binders(
      env_ctx.clone(),
      Vec::new(),
      "(A: Sort 0) (a b c: Unknown):",
    );
    assert!(res.is_err());
    match res.unwrap_err() {
      Err::Error(_err) => {
        // TODO(rish) check the error:
        //        assert_eq!(
        //          err.errors, vec![ParseErrorKind::UndefinedReference(
        //              Name::from("Unknown"),
        //              Vector::from(vec![Name::from("A")])
        //            ), Nom(Tag)]
        //        )
      }
      _ => {
        assert!(false)
      }
    }
  }

  #[test]
  fn test_parse_pi() {
    let env_ctx = Rc::new(RefCell::new(Env::new()));
    fn test(env_ctx: EnvCtx, i: &str) -> IResult<Span, Expr, ParseError<Span>> {
      parse_expr(Vector::new(), Vector::new(), OrdMap::new(), env_ctx)(
        Span::new(i),
      )
    }
    let res = test(env_ctx.clone(), "∀ (a: Sort 0) -> Sort 0");
    assert!(res.is_ok());
    let res = test(env_ctx.clone(), "∀ (A: Sort 0) (x : A) -> A");
    println!("{:?}", res);
    assert!(res.is_ok());
  }

  #[test]
  fn test_parse_let() {
    let env_ctx = Rc::new(RefCell::new(Env::new()));
    fn test(env_ctx: EnvCtx, i: &str) -> IResult<Span, Expr, ParseError<Span>> {
      parse_expr(Vector::new(), Vector::new(), OrdMap::new(), env_ctx)(
        Span::new(i),
      )
    }
    let res = test(env_ctx.clone(), "let recname : Sort 0 := #Str in recname");
    print!("{:?}", res);
    assert!(res.is_ok());
  }

  #[test]
  fn test_parse_lam() {
    fn test(i: &str) -> IResult<Span, Expr, ParseError<Span>> {
      parse_expr(Vector::new(), Vector::new(), OrdMap::new(), Rc::new(RefCell::new(Env::new())))(
        Span::new(i),
      )
    }
    let res = test("λ (a: Sort 0) => Sort 0");
    assert!(res.is_ok());
    let res = test("λ (A: Sort 0) (x : A) => A");
    assert!(res.is_ok());
    let res = test(
      "λ [X: Sort 0] {X: Sort 0} (A: Sort 0) (x : A) => A",
    );
    assert!(res.is_ok());

    //"in" (and other reserved keywords) should not be considered
    //the end of an application sequence unless followed by a space/newline/EOF
    let res = test(
      "λ [test: λ (inname : Sort 0) => inname inname] => Sort 0"
    );
    assert!(res.is_ok());
  }

  #[test]
  fn test_parse_bound_expression() {
    fn test(i: &str, rec: Option<Name>) -> IResult<Span, (Expr, Expr), ParseError<Span>> {
      parse_bound_expression(Vector::new(), Vector::new(), OrdMap::new(), Rc::new(RefCell::new(Env::new())),
        rec)(Span::new(i))
    }
    let res = test("(a: Sort 0) : Sort 0 := a", Option::None);
    assert!(res.is_ok());
    let (_, (typ, trm)) = res.unwrap();
    assert_eq!(typ,
      Expr::Pi(Name::from("a"), BinderInfo::Default, 
        Box::new(
          Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap()),
        ),
        Box::new(
          Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap()),
        ),
      )
    );
    assert_eq!(trm,
      Expr::Lam(Name::from("a"), BinderInfo::Default, 
        Box::new(
          Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap()),
        ),
        Box::new(
          Expr::Var(Name::from("a"), 0u32.into())
        ),
      )
    );

    let res = test("(a b: Sort 0) : Sort 0 := f a b", Option::Some(Name::from("f")));
    assert!(res.is_ok());
    let (_, (typ, trm)) = res.unwrap();
    assert_eq!(typ,
      Expr::Pi(Name::from("a"), BinderInfo::Default, 
        Box::new(
          Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap()),
        ),
        Box::new(
          Expr::Pi(Name::from("b"), BinderInfo::Default, 
            Box::new(
              Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap()),
            ),
            Box::new(
              Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap()),
            ),
          )
        ),
      )
    );
    assert_eq!(trm,
      Expr::Fix(Name::from("f"),
        Box::new(
          Expr::Lam(Name::from("a"), BinderInfo::Default, 
            Box::new(
              Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap()),
            ),
            Box::new(
              Expr::Lam(Name::from("b"), BinderInfo::Default, 
                Box::new(
                  Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap()),
                ),
                Box::new(
                  Expr::App(
                    Box::new(
                      Expr::App(
                        Box::new(
                          Expr::Var(Name::from("f"), 2u32.into())
                        ),
                        Box::new(
                          Expr::Var(Name::from("a"), 1u32.into())
                        )
                      )
                    ),
                    Box::new(
                      Expr::Var(Name::from("b"), 0u32.into())
                    )
                  )
                )
              )
            )
          )
        )
      )
    );
  }

  #[quickcheck]
  fn prop_expr_parse_print(x: ExprEnv) -> bool {
    let s = x.expr.pretty(&x.env, false);
    println!("input: \t\t{s}");
    let res = parse_expr_apps(dummy_univ_ctx(), Vector::new(), dummy_global_ctx(), Rc::new(RefCell::new(Env::new())))(Span::new(&s));
    match res {
      Ok((_, y)) => {
        println!("re-parsed: \t{}", y.pretty(&x.env, false));
        x.expr == y
      }
      Err(e) => {
        println!("err: {:?}", e);
        false
      }
    }
  }
}
