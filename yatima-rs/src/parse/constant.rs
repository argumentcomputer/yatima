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
      parse_u8,
      store_expr,
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
};

pub fn parse_levels(i: Span) -> IResult<Span, Vec<Name>, ParseError<Span>> {
  let (i, _) = tag("{")(i)?;
  let (i, args) = many0(preceded(parse_space, parse_name))(i)?;
  let (i, _) = parse_space(i)?;
  let (i, _) = tag("}")(i)?;
  Ok((i, args))
}

/// Parses an axiom constant
/// `unsafe axiom foo : A`
pub fn parse_const_axiom(
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Const, ParseError<Span>> {
  move |from: Span| {
    let (i, safe) = alt((
      value(false, terminated(tag("unsafe"), parse_space)),
      success(true),
    ))(from)?;
    let (i, _) = tag("axiom")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, name) = parse_name(i)?;
    let (i, _) = parse_space(i)?;
    let (i, lvl) = parse_levels(i)?;
    let (i, _) = parse_space(i)?;
    let (upto, typ) = parse_expr(
      Vector::from(lvl.clone()),
      Vector::new(),
      global_ctx.clone(),
      env_ctx.clone(),
    )(i)?;
    let (i, typ) = store_expr(env_ctx.clone(), typ, i)?;
    Ok((upto, Const::Axiom { name, lvl, typ, safe }))
  }
}

/// Parses a theorem constant
/// `theorem foo : A := proof`
pub fn parse_const_theorem(
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Const, ParseError<Span>> {
  move |from: Span| {
    let (i, _) = tag("theorem")(from)?;
    let (i, _) = parse_space(i)?;
    let (i, name) = parse_name(i)?;
    let (i, _) = parse_space(i)?;
    let (i, lvl) = parse_levels(i)?;
    let (i, _) = parse_space(i)?;
    let (upto, (typ, expr)) = parse_bound_expression(
      Vector::from(lvl.clone()),
      Vector::new(),
      global_ctx.clone(),
      env_ctx.clone(),
      None,
    )(i)?;
    let (i, typ) = store_expr(env_ctx.clone(), typ, i)?;
    let (i, expr) = store_expr(env_ctx.clone(), expr, i)?;
    Ok((upto, Const::Theorem { name, lvl, typ, expr }))
  }
}

/// Parses an opaque constant
/// `unsafe opaque rec foo : A := body`
pub fn parse_const_opaque(
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Const, ParseError<Span>> {
  move |from: Span| {
    let (i, safe) = alt((
      value(false, terminated(tag("unsafe"), parse_space)),
      success(true),
    ))(from)?;
    let (i, _) = tag("opaque")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, rec) = opt(tag("rec"))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, name) = parse_name(i)?;
    let rec = rec.map(|_| name.clone());
    let (i, lvl) = parse_levels(i)?;
    let (i, _) = parse_space(i)?;
    let (upto, (typ, expr)) = parse_bound_expression(
      Vector::from(lvl.clone()),
      Vector::new(),
      global_ctx.clone(),
      env_ctx.clone(),
      rec,
    )(i)?;
    let (i, typ) = store_expr(env_ctx.clone(), typ, i)?;
    let (i, expr) = store_expr(env_ctx.clone(), expr, i)?;
    Ok((upto, Const::Opaque { name, lvl, typ, expr, safe }))
  }
}

/// Parses a definition constant
/// `partial def rec foo : A := body`
pub fn parse_const_def(
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Const, ParseError<Span>> {
  move |from: Span| {
    let (i, safe) = alt((
      value(DefSafety::Unsafe, terminated(tag("unsafe"), parse_space)),
      value(DefSafety::Partial, terminated(tag("partial"), parse_space)),
      success(DefSafety::Safe),
    ))(from)?;
    let (i, _) = tag("def")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, rec) = opt(tag("rec"))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, name) = parse_name(i)?;
    let rec = rec.map(|_| name.clone());
    let (i, _) = parse_space(i)?;
    let (i, lvl) = parse_levels(i)?;
    let (i, _) = parse_space(i)?;
    let (upto, (typ, expr)) = parse_bound_expression(
      Vector::from(lvl.clone()),
      Vector::new(),
      global_ctx.clone(),
      env_ctx.clone(),
      rec,
    )(i)?;
    let (i, typ) = store_expr(env_ctx.clone(), typ, i)?;
    let (i, expr) = store_expr(env_ctx.clone(), expr, i)?;
    Ok((upto, Const::Definition { name, lvl, typ, expr, safe }))
  }
}

/// ```lean
/// unsafe inductive rec Vector {u} (A: Sort 0) : ∀ (k: Nat) -> Sort 0 where
/// | Nil : Vector A Nat.zero,
/// | Cons (k: Nat) (x: A) (xs: Vector A k): Vector A (Nat.succ k),
/// ```
/// TODO: nest, refl
struct InductiveDecl {
  safe: bool,
  recr: bool,
  name: Name,
  lvl: Vec<Name>,
  params: Vec<(BinderInfo, Name, Expr)>,
  indices: Vec<(BinderInfo, Name, Expr)>,
  typ: Expr,
  ctors: Vec<(Name, Expr)>,
}

// TODO: tentative
pub fn parse_const_inductive_decl(
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, InductiveDecl, ParseError<Span>> {
  move |from: Span| {
    let (i, safe) = alt((
      value(false, terminated(tag("unsafe"), parse_space)),
      success(true),
    ))(from)?;
    let (i, _) = tag("inductive")(from)?;
    let (i, _) = parse_space(i)?;
    let (i, rec) = opt(tag("rec"))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, name) = parse_name(i)?;
    let rec = rec.map(|_| name.clone());
    let (i, lvl) = parse_levels(i)?;
    let (i, _) = parse_space(i)?;
    let univ_ctx = Vector::from(lvl.clone());
    let (i, params) = parse_binders0(
      univ_ctx.clone(),
      Vector::new(),
      global_ctx.clone(),
      env_ctx.clone(),
      vec![':'],
    )(i)?;
    let (i, _) = parse_space(i)?;
    let (i, _) = tag(":")(i)?;
    let (i, _) = parse_space(i)?;
    let bind_ctx: Vector<Name> =
      params.iter().map(|(_, n, _)| n.clone()).collect();
    let (i, indices) = parse_binders0(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
      vec!['-'],
    )(i)?;
    let mut bind_ctx = bind_ctx;
    for (_, n, _) in indices.iter() {
      bind_ctx.push_front(n.clone());
    }
    let (i, _) = if indices.len() != 0 {
      let (i, _) = tag("->")(i)?;
      let (i, _) = parse_space(i)?;
      Ok((i, ()))
    }
    else {
      Ok((i, ()))
    }?;
    let (i, typ) = parse_expr(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
    )(i)?;
    let typ = params
      .clone()
      .into_iter()
      .chain(indices.clone().into_iter())
      .rev()
      .fold(typ, |acc, (b, n, t)| Expr::Pi(n, b, Box::new(t), Box::new(acc)));
    let (i, _) = tag("where")(i)?;
    let (i, ctors) = many0(terminated(
      parse_const_inductive_ctor(
        univ_ctx.clone(),
        bind_ctx.clone(),
        global_ctx.clone(),
        env_ctx.clone(),
      ),
      parse_space,
    ))(i)?;

    Ok((i, InductiveDecl {
      name,
      lvl,
      typ,
      params,
      indices,
      ctors,
      recr: rec.is_some(),
      safe,
    }))
  }
}

// TODO: tentative
pub fn parse_const_inductive_ctor(
  univ_ctx: UnivCtx,
  bind_ctx: BindCtx,
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, (Name, Expr), ParseError<Span>> {
  move |from: Span| {
    let (i, _) = tag("|")(from)?;
    let (i, _) = parse_space(i)?;
    let (i, nam) = parse_name(i)?;
    let (i, _) = parse_space(i)?;
    let (i, _) = tag(":")(i)?;
    let (i, typ) = parse_expr(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
    )(i)?;
    let (i, _) = tag(",")(i)?;
    Ok((i, (nam, typ)))
  }
}
