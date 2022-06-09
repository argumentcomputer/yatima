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
      parse_space1,
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
  parse_expr_apps,
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
    let (i, lvl) = opt(parse_levels)(i)?;
    let lvl = match lvl {
      Option::None => vec![],
      Option::Some(l) => l
    };
    let (i, _) = parse_space(i)?;
    let (i, _) = tag(":")(i)?;
    let (i, _) = parse_space(i)?;
    let (upto, typ) = parse_expr_apps(
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
    let (i, lvl) = opt(parse_levels)(i)?;
    let lvl = match lvl {
      Option::None => vec![],
      Option::Some(l) => l
    };
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
      value(false, terminated(tag("unsafe"), parse_space1)),
      success(true),
    ))(from)?;
    let (i, _) = tag("opaque")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, rec) = opt(tag("rec"))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, name) = parse_name(i)?;
    let rec = rec.map(|_| name.clone());
    let (i, _) = parse_space(i)?;
    let (i, lvl) = opt(parse_levels)(i)?;
    let lvl = match lvl {
      Option::None => vec![],
      Option::Some(l) => l
    };
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
      value(DefSafety::Unsafe, terminated(tag("unsafe"), parse_space1)),
      value(DefSafety::Partial, terminated(tag("partial"), parse_space1)),
      success(DefSafety::Safe),
    ))(from)?;
    let (i, _) = tag("def")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, rec) = opt(tag("rec"))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, name) = parse_name(i)?;
    let rec = rec.map(|_| name.clone());
    let (i, _) = parse_space(i)?;
    let (i, lvl) = opt(parse_levels)(i)?;
    let lvl = match lvl {
      Option::None => vec![],
      Option::Some(l) => l
    };
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
#[derive(Clone, Debug, PartialEq)]
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
fn parse_const_inductive_decl(
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, InductiveDecl, ParseError<Span>> {
  move |from: Span| {
    let (i, safe) = alt((
      value(false, terminated(tag("unsafe"), parse_space)),
      success(true),
    ))(from)?;
    let (i, _) = tag("inductive")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, rec) = opt(tag("rec"))(i)?;
    let (i, _) = parse_space(i)?;
    let (i, name) = parse_name(i)?;
    let (i, _) = parse_space(i)?;
    let rec = rec.map(|_| name.clone());
    let (i, lvl) = opt(parse_levels)(i)?;
    let lvl = match lvl {
      Option::None => vec![],
      Option::Some(l) => l
    };
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

    let mut ctor_bind_ctx = Vector::new();
    // the inductive type name is an implicitly bound variable
    // within each constructor declaration; this is replaced
    // with a reference to the inductive type constant when generating
    // the constructor constant
    ctor_bind_ctx.push_front(name.clone());

    let mut bind_ctx = Vector::new();

    for (_, n, _) in params.iter() {
      ctor_bind_ctx.push_front(n.clone());
      bind_ctx.push_front(n.clone());
    }

    let (i, parsed_indices) = opt(parse_binders0(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
      vec!['-', '→'],
    ))(i)?;
    let indices = 
      match parsed_indices {
        Some(i) => i,
        None => Vec::new()
      };

    let mut bind_ctx = bind_ctx;
    for (_, n, _) in indices.iter() {
      bind_ctx.push_front(n.clone());
    }
    let (i, _) = parse_space(i)?;

    let (i, _) = if indices.len() != 0 {
      let (i, _) = alt((tag("->"), tag("→")))(i)?;
      let (i, _) = parse_space(i)?;
      Ok((i, ()))
    }
    else {
      Ok((i, ()))
    }?;

    let (i, typ) = parse_expr_apps(
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
    let (i, _) = parse_space(i)?;
    let (i, _) = tag("where")(i)?;
    let (i, _) = parse_space(i)?;
    let (i, ctors) = many0(terminated(
      parse_const_inductive_ctor(
        univ_ctx.clone(),
        ctor_bind_ctx,
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

pub fn inductive_decl_to_const_inductive(
  env: &mut Env,
  typ: &Expr,
  ctors: &Vec<(Name, Expr)>
) -> Result<(ExprCid, Vec<(Name, ExprCid)>), EnvError> {
  let typcid = typ.clone().store(env)?;
  let constcids = ctors.iter().fold(Ok(Vec::new()),
    |acc, (name, expr)| {
      let mut cids = acc?;
      let cid = expr.clone().store(env)?;
      cids.push((name.clone(), cid));
      Ok(cids)
    })?;
    Ok((typcid, constcids))
}

pub fn parse_const_inductive(
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Const, ParseError<Span>> {
  move |from: Span| {
    let (i, ind) = parse_const_inductive_decl(global_ctx.clone(), env_ctx.clone())(from)?;
    let mut env = env_ctx.try_borrow_mut().map_err(|e| {
      Err::Error(ParseError::new(
        i,
        ParseErrorKind::EnvBorrowMut(format!("{}", e)),
      ))
    })?;

    let (typcid, ctorcids) = inductive_decl_to_const_inductive(&mut env, &ind.typ, &ind.ctors).map_err(|e| {
      Err::Error(ParseError::new(i, ParseErrorKind::Env(format!("{:?}", e))))
    })?;

    Ok((i, Const::Inductive {
      name: ind.name,
      lvl: ind.lvl,
      typ: typcid,
      params: ind.params.len(),
      indices: ind.indices.len(),
      ctors: ctorcids,
      recr: ind.recr,
      safe: ind.safe,
      nest: false,
      refl: false,
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
    let (i, bs) = parse_binders0(
      univ_ctx.clone(),
      bind_ctx.clone(),
      global_ctx.clone(),
      env_ctx.clone(),
      vec![':'],
    )(i)?;

    let mut bind_ctx_final = bind_ctx.clone();
    for (_, n, _) in bs.iter() {
      bind_ctx_final.push_front(n.clone());
    }

    let (i, _) = parse_space(i)?;
    let (i, _) = tag(":")(i)?;
    let (i, _) = parse_space(i)?;

    let (i, typ) = parse_expr_apps(
      univ_ctx.clone(),
      bind_ctx_final,
      global_ctx.clone(),
      env_ctx.clone(),
    )(i)?;

    let typ = bs
      .clone()
      .into_iter()
      .rev()
      .fold(typ, |acc, (b, n, t)| Expr::Pi(n, b, Box::new(t), Box::new(acc)));

    let (i, _) = tag(",")(i)?;
    Ok((i, (nam, typ)))
  }
}

/// Parses each term variant
pub fn parse_const(
  global_ctx: GlobalCtx,
  env_ctx: EnvCtx,
) -> impl Fn(Span) -> IResult<Span, Const, ParseError<Span>> {
  move |i: Span| {
    alt((
      parse_const_inductive(
        global_ctx.clone(),
        env_ctx.clone(),
      ),
      parse_const_def(
        global_ctx.clone(),
        env_ctx.clone(),
      ),
      parse_const_opaque(
        global_ctx.clone(),
        env_ctx.clone(),
      ),
      parse_const_theorem(
        global_ctx.clone(),
        env_ctx.clone(),
      ),
      parse_const_axiom(
        global_ctx.clone(),
        env_ctx.clone(),
      ),
    ))(i)
  }
}

#[cfg(test)]
pub mod tests {
  use alloc::rc::Rc;
  use super::*;
  use multihash::{
    Code,
    MultihashDigest,
  };

  use crate::constant::tests::ConstEnv;

  #[test]
  fn test_parse_levels() {
    fn test(i: &str) -> IResult<Span, Vec<Name>, ParseError<Span>> {
      parse_levels(Span::new(i))
    }

    let res = test("{}");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, vec![]);

    let res = test("{u}");
    assert_eq!(res.unwrap().1, vec![Name::from("u")]);

    let res = test("{u v}");
    assert_eq!(res.unwrap().1, vec![Name::from("u"), Name::from("v")]);
  }

  fn dummy_typ() -> Expr {
    Expr::Sort(Univ::Zero.cid(&mut Env::new()).unwrap())
  }

  fn dummy_typ_cid() -> ExprCid {
    dummy_typ().store(&mut Env::new()).unwrap()
  }

  fn dummy_fix_typ_cid(name: Name) -> ExprCid {
    Expr::Fix(name, Box::new(dummy_typ())).store(&mut Env::new()).unwrap()
  }

  #[test]
  fn test_parse_axiom() {
    fn test(i: &str) -> IResult<Span, Const, ParseError<Span>> {
      let env_ctx = Rc::new(RefCell::new(Env::new()));
      let global_ctx = OrdMap::new();
      parse_const_axiom(global_ctx, env_ctx)(Span::new(i))
    }

    let res = test("axiom foo {u v} : Sort 0");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Const::Axiom {
      name: Name::from("foo"),
      lvl: vec![Name::from("u"), Name::from("v")],
      typ: dummy_typ_cid(),
      safe: true
    });

    let res = test("unsafe axiom foo : Sort 0");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Const::Axiom {
      name: Name::from("foo"),
      lvl: vec![],
      typ: dummy_typ_cid(),
      safe: false
    });
  }

  #[test]
  fn test_parse_theorem() {
    fn test(i: &str) -> IResult<Span, Const, ParseError<Span>> {
      let env_ctx = Rc::new(RefCell::new(Env::new()));
      let global_ctx = OrdMap::new();
      parse_const_theorem(global_ctx, env_ctx)(Span::new(i))
    }

    let res = test("theorem foo {u v} : Sort 0 := Sort 0");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Const::Theorem {
      name: Name::from("foo"),
      lvl: vec![Name::from("u"), Name::from("v")],
      typ: dummy_typ_cid(),
      expr: dummy_typ_cid()
    });
  }

  #[test]
  fn test_parse_opaque() {
    fn test(i: &str) -> IResult<Span, Const, ParseError<Span>> {
      let env_ctx = Rc::new(RefCell::new(Env::new()));
      let global_ctx = OrdMap::new();
      parse_const_opaque(global_ctx, env_ctx)(Span::new(i))
    }

    let res = test("opaque foo {u v} : Sort 0 := Sort 0");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Const::Opaque {
      name: Name::from("foo"),
      lvl: vec![Name::from("u"), Name::from("v")],
      typ: dummy_typ_cid(),
      expr: dummy_typ_cid(),
      safe: true
    });

    let res = test("unsafe opaque rec foo {u v} : Sort 0 := Sort 0");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Const::Opaque {
      name: Name::from("foo"),
      lvl: vec![Name::from("u"), Name::from("v")],
      typ: dummy_typ_cid(),
      expr: dummy_fix_typ_cid(Name::from("foo")),
      safe: false
    });
  }

  #[test]
  fn test_parse_def() {
    fn test(i: &str) -> IResult<Span, Const, ParseError<Span>> {
      let env_ctx = Rc::new(RefCell::new(Env::new()));
      let global_ctx = OrdMap::new();
      parse_const_def(global_ctx, env_ctx)(Span::new(i))
    }

    let res = test("def foo {u v} : Sort 0 := Sort 0");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Const::Definition {
      name: Name::from("foo"),
      lvl: vec![Name::from("u"), Name::from("v")],
      typ: dummy_typ_cid(),
      expr: dummy_typ_cid(),
      safe: DefSafety::Safe
    });

    let res = test("unsafe def rec foo {u v} : Sort 0 := Sort 0");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Const::Definition {
      name: Name::from("foo"),
      lvl: vec![Name::from("u"), Name::from("v")],
      typ: dummy_typ_cid(),
      expr: dummy_fix_typ_cid(Name::from("foo")),
      safe: DefSafety::Unsafe
    });

    let res = test("partial def foo : Sort 0 := Sort 0");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, Const::Definition {
      name: Name::from("foo"),
      lvl: vec![],
      typ: dummy_typ_cid(),
      expr: dummy_typ_cid(),
      safe: DefSafety::Partial
    });
  }

  use crate::expression::tests::{dummy_global_ctx, dummy_const_cid};

  #[test]
  fn test_parse_inductive_decl() {
    fn test(i: &str) -> IResult<Span, InductiveDecl, ParseError<Span>> {
      let env_ctx = Rc::new(RefCell::new(Env::new()));
      parse_const_inductive_decl(dummy_global_ctx(), env_ctx)(Span::new(i))
    }

    let nat = Expr::Const(Name::from("Nat"), dummy_const_cid(1), vec![]);
    let nat_zero = Expr::Const(Name::from("Nat.zero"), dummy_const_cid(2), vec![]);
    let nat_succ = Expr::Const(Name::from("Nat.succ"), dummy_const_cid(3), vec![]);

    //TODO(rish) clean up notation (comma at the end),
    //also split this big test up into its unit test components
    let res = test(
    "unsafe inductive rec Vector {u} (A: Sort 0) : (k: Nat) -> Sort 0 where
     | Nil : Vector A Nat.zero,
     | Cons (k: Nat) (x: A) (xs: Vector A k): Vector A (Nat.succ k),");
    assert!(res.is_ok());
    assert_eq!(res.unwrap().1, InductiveDecl {
      safe: false,
      recr: true,
      name: Name::from("Vector"),
      lvl: vec![Name::from("u")],
      params: vec![(BinderInfo::Default, Name::from("A"), dummy_typ())],
      indices: vec![(BinderInfo::Default, Name::from("k"), nat.clone())],
      typ: Expr::Pi(Name::from("A"), BinderInfo::Default, Box::new(dummy_typ()),
      Box::new(Expr::Pi(Name::from("k"), BinderInfo::Default, Box::new(nat.clone()), Box::new(dummy_typ())))),
      ctors: vec![
        (Name::from("Nil"),
          Expr::App(
            Box::new(Expr::App(
            Box::new(Expr::Var(Name::from("Vector"), 1u32.into())),
            Box::new(Expr::Var(Name::from("A"), 0u32.into())))),
            Box::new(nat_zero.clone())),
          ),
        (Name::from("Cons"),
          Expr::Pi(Name::from("k"), BinderInfo::Default, Box::new(nat.clone()),
          Box::new(
          Expr::Pi(Name::from("x"), BinderInfo::Default, Box::new(Expr::Var(Name::from("A"), 1u32.into())),
          Box::new(
          Expr::Pi(Name::from("xs"), BinderInfo::Default, 
            Box::new(Expr::App(
            Box::new(Expr::App(
            Box::new(Expr::Var(Name::from("Vector"), 3u32.into())),
            Box::new(Expr::Var(Name::from("A"), 2u32.into())))),
            Box::new(
              Expr::Var(Name::from("k"), 1u32.into())),
          )),
          Box::new(
          Expr::App(
            Box::new(Expr::App(
            Box::new(Expr::Var(Name::from("Vector"), 4u32.into())),
            Box::new(Expr::Var(Name::from("A"), 3u32.into())))),
            Box::new(
              Expr::App(
              Box::new(nat_succ.clone()),
              Box::new(Expr::Var(Name::from("k"), 2u32.into())))),
          ))))))),
        ),
      ]
    });
  }

  #[quickcheck]
  fn prop_const_parse_print(x: ConstEnv) -> bool {
    let s = x.cnst.pretty(&x.env, false).unwrap();
    println!("input: \t\t{s}");
    let res_env = Rc::new(RefCell::new(Env::new()));
    let res = parse_const(dummy_global_ctx(), res_env.clone())(Span::new(&s));
    match res {
      Ok((_, y)) => {
        println!("re-parsed: \t{}", y.pretty(&*res_env.borrow(), false).unwrap());
        x.cnst == y
      }
      Err(e) => {
        println!("err: {:?}", e);
        false
      }
    }
  }
}
