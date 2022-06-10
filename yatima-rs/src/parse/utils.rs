use crate::parse::{
  base,
  error::{
    ParseError,
    ParseErrorKind,
  },
  span::Span,
};
use core::ops::DerefMut;

use crate::{
  environment::{
    ConstCid,
    Env,
    ExprCid,
    UnivCid,
  },
  constant::Const,
  expression::{
    Expr,
    BinderInfo,
  },
  name::Name,
  nat::Nat,
  universe::Univ,
};

use im::{
  OrdMap,
  Vector,
};

use nom::{
  branch::alt,
  bytes::complete::{
    tag,
    take_till,
    take_till1,
  },
  character::complete::{
    multispace0,
    multispace1,
  },
  combinator::{
    eof,
    peek,
    value,
  },
  multi::{
    many0,
    fold_many0
  },
  sequence::{
    terminated,
    preceded,
    pair,
  },
  Err,
  IResult,
};

use alloc::{
  rc::Rc,
  string::String,
};
use core::cell::RefCell;

pub type UnivCtx = Vector<Name>;
pub type BindCtx = Vector<Name>;
pub type GlobalCtx = OrdMap<Name, ConstCid>;
pub type EnvCtx = Rc<RefCell<Env>>;

/// Returns a list of reserved Yatima symbols
pub fn reserved_symbols() -> Vec<String> {
  Vec::from(vec![
    String::from("--"),
    String::from("-/"),
    String::from("/-"),
    String::from("λ"),
    String::from("=>"),
    String::from("Π"),
    String::from("->"),
    String::from("let"),
    String::from("in"),
    String::from("def"),
    String::from("axiom"),
    String::from("theorem"),
    String::from("opaque"),
    String::from("inductive"),
  ])
}

pub fn parse_nat(from: Span) -> IResult<Span, Nat, ParseError<Span>> {
  let base = base::LitBase::Dec;
  let (i, digits) = base::parse_litbase_digits(base)(from)?;
  match base_x::decode(base.base_digits(), &digits) {
    Ok(bytes) => Ok((i, Nat::from_bytes_be(&bytes))),
    Err(_) => Err(nom::Err::Error(ParseError::new(
      i,
      ParseErrorKind::InvalidBaseEncoding(base),
    ))),
  }
}

pub fn parse_u8(from: Span) -> IResult<Span, u8, ParseError<Span>> {
  let base = base::LitBase::Dec;
  let (i, digits) = base::parse_litbase_digits(base)(from)?;
  match base_x::decode(base.base_digits(), &digits) {
    Ok(_) => {
      use ParseErrorKind::ParseIntErr;
      let x = u8::from_str_radix(&digits, base.radix()).map_or_else(
        |e| Err(nom::Err::Error(ParseError::new(from, ParseIntErr(e)))),
        Ok,
      )?;
      Ok((i, x))
    }
    Err(_) => Err(nom::Err::Error(ParseError::new(
      i,
      ParseErrorKind::InvalidBaseEncoding(base),
    ))),
  }
}

pub fn parse_u16(from: Span) -> IResult<Span, u16, ParseError<Span>> {
  let base = base::LitBase::Dec;
  let (i, digits) = base::parse_litbase_digits(base)(from)?;
  match base_x::decode(base.base_digits(), &digits) {
    Ok(_) => {
      use ParseErrorKind::ParseIntErr;
      let x = u16::from_str_radix(&digits, base.radix()).map_or_else(
        |e| Err(nom::Err::Error(ParseError::new(from, ParseIntErr(e)))),
        Ok,
      )?;
      Ok((i, x))
    }
    Err(_) => Err(nom::Err::Error(ParseError::new(
      i,
      ParseErrorKind::InvalidBaseEncoding(base),
    ))),
  }
}

pub fn parse_u64(from: Span) -> IResult<Span, u64, ParseError<Span>> {
  let base = base::LitBase::Dec;
  let (i, digits) = base::parse_litbase_digits(base)(from)?;
  match base_x::decode(base.base_digits(), &digits) {
    Ok(_) => {
      use ParseErrorKind::ParseIntErr;
      let x = u64::from_str_radix(&digits, base.radix()).map_or_else(
        |e| Err(nom::Err::Error(ParseError::new(from, ParseIntErr(e)))),
        Ok,
      )?;
      Ok((i, x))
    }
    Err(_) => Err(nom::Err::Error(ParseError::new(
      i,
      ParseErrorKind::InvalidBaseEncoding(base),
    ))),
  }
}

pub fn parse_text(from: Span) -> IResult<Span, String, ParseError<Span>> {
  let (i, s) = take_till1(|x| char::is_whitespace(x))(from)?;
  let s: String = String::from(s.fragment().clone());
  Ok((i, s))
}

/// Parses a line comment
pub fn parse_line_comment(i: Span) -> IResult<Span, Span, ParseError<Span>> {
  let (i, _) = tag("--")(i)?;
  let (i, com) = take_till(|c| c == '\n')(i)?;
  Ok((i, com))
}

/// Parses zero or more spaces or control characters
pub fn parse_space(i: Span) -> IResult<Span, Vec<Span>, ParseError<Span>> {
  let (i, _) = multispace0(i)?;
  let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
  Ok((i, com))
}

/// Parses one or more spaces or control characters
pub fn parse_space1(i: Span) -> IResult<Span, Vec<Span>, ParseError<Span>> {
  let (i, _) = multispace1(i)?;
  let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
  Ok((i, com))
}

/// Parses a name
pub fn parse_name(from: Span) -> IResult<Span, Name, ParseError<Span>> {
  let parse_word = take_till1(|x| {
    char::is_whitespace(x)
      | (x == ':')
      | (x == ';')
      | (x == ')')
      | (x == '(')
      | (x == '{')
      | (x == '}')
      | (x == '[')
      | (x == ']')
      | (x == ',')
      | (x == '.')
  });
  let (i, (s1, s2)) = pair(&parse_word, fold_many0(preceded(tag("."), &parse_word), String::new,
    |acc: String, res: nom_locate::LocatedSpan<&str>| {format!("{}.{}", acc, res.fragment())}))(from)?;
  let s: String = String::from(s1.fragment().to_owned()) + &s2;
  if reserved_symbols().contains(&s) {
    Err(Err::Error(ParseError::new(from, ParseErrorKind::ReservedKeyword(s))))
  }
  else if s.starts_with('#') {
    Err(Err::Error(ParseError::new(from, ParseErrorKind::ReservedSyntax(s))))
  }
  else if is_numeric_symbol_string1(&s) | is_numeric_symbol_string2(&s) {
    Err(Err::Error(ParseError::new(from, ParseErrorKind::NumericSyntax(s))))
  }
  else if !is_valid_symbol_string(&s) {
    Err(Err::Error(ParseError::new(from, ParseErrorKind::InvalidSymbol(s))))
  }
  else {
    Ok((i, Name::from(s)))
  }
}

/// Checks if a string represents an unsigned number
pub fn is_numeric_symbol_string1(s: &str) -> bool {
  s.starts_with('0')
    || s.starts_with('1')
    || s.starts_with('2')
    || s.starts_with('3')
    || s.starts_with('4')
    || s.starts_with('5')
    || s.starts_with('6')
    || s.starts_with('7')
    || s.starts_with('8')
    || s.starts_with('9')
}

/// Checks if a string represents a signed number
pub fn is_numeric_symbol_string2(s: &str) -> bool {
  s.starts_with("-0")
    || s.starts_with("-1")
    || s.starts_with("-2")
    || s.starts_with("-3")
    || s.starts_with("-4")
    || s.starts_with("-5")
    || s.starts_with("-6")
    || s.starts_with("-7")
    || s.starts_with("-8")
    || s.starts_with("-9")
    || s.starts_with("+0")
    || s.starts_with("+1")
    || s.starts_with("+2")
    || s.starts_with("+3")
    || s.starts_with("+4")
    || s.starts_with("+5")
    || s.starts_with("+6")
    || s.starts_with("+7")
    || s.starts_with("+8")
    || s.starts_with("+9")
}

/// Checks if a char represents a valid syntactical character
pub fn is_valid_symbol_char(c: char) -> bool {
  c != ':'
    && c != ';'
    && c != '('
    && c != ')'
    && c != '{'
    && c != '}'
    && c != ']'
    && c != '['
    && c != ','
    && !char::is_whitespace(c)
    && !char::is_control(c)
}

/// Checks if a string represents valid text
pub fn is_valid_symbol_string(s: &str) -> bool {
  let invalid_chars = s.starts_with('"')
    || s.starts_with('\'')
    || s.starts_with('#')
    || s.chars().any(|x| !is_valid_symbol_char(x));
  !s.is_empty() && !invalid_chars
}

/// Parses a syntactical character
pub fn parse_builtin_symbol_end()
-> impl Fn(Span) -> IResult<Span, (), ParseError<Span>> {
  move |from: Span| {
    alt((
      peek(value((), parse_space1)),
      peek(value((), eof)),
      peek(value((), tag("("))),
      peek(value((), tag(")"))),
      peek(value((), tag("{"))),
      peek(value((), tag("}"))),
      peek(value((), tag("["))),
      peek(value((), tag("]"))),
      peek(value((), tag(";"))),
      peek(value((), tag(":"))),
      peek(value((), tag(","))),
    ))(from)
  }
}

pub fn store_univ(
  env_ctx: EnvCtx,
  univ: Univ,
  i: Span,
) -> IResult<Span, UnivCid, ParseError<Span>> {
  let mut env = env_ctx.try_borrow_mut().map_err(|e| {
    Err::Error(ParseError::new(
      i,
      ParseErrorKind::EnvBorrowMut(format!("{}", e)),
    ))
  })?;
  let univ = univ.store(env.deref_mut()).map_err(|e| {
    Err::Error(ParseError::new(i, ParseErrorKind::Env(format!("{:?}", e))))
  })?;
  Ok((i, univ))
}

pub fn store_expr(
  env_ctx: EnvCtx,
  expr: Expr,
  i: Span,
) -> IResult<Span, ExprCid, ParseError<Span>> {
  let mut env = env_ctx.try_borrow_mut().map_err(|e| {
    Err::Error(ParseError::new(
      i,
      ParseErrorKind::EnvBorrowMut(format!("{}", e)),
    ))
  })?;
  let expr = expr.store(env.deref_mut()).map_err(|e| {
    Err::Error(ParseError::new(i, ParseErrorKind::Env(format!("{:?}", e))))
  })?;
  Ok((i, expr))
}

pub fn store_const(
  env_ctx: EnvCtx,
  cnst: Const,
  i: Span,
) -> IResult<Span, ConstCid, ParseError<Span>> {
  let mut env = env_ctx.try_borrow_mut().map_err(|e| {
    Err::Error(ParseError::new(
      i,
      ParseErrorKind::EnvBorrowMut(format!("{}", e)),
    ))
  })?;
  let cnstcid = cnst.store(env.deref_mut()).map_err(|e| {
    Err::Error(ParseError::new(i, ParseErrorKind::Env(format!("{:?}", e))))
  })?;
  Ok((i, cnstcid))
}

/// The input `Vector : ∀ (A: Type) -> ∀ (n: Nat) -> Sort 0` with depth 1 returns:
///   - string: `(A: Type)` 
///   - type: `∀ (n: Nat) -> Sort 0`
/// This is useful for printing defs
/// sort of the inverse of parse_bound_expressions?
/// Note that this doesn't fail -- it just stops parsing if it hits a non-pi expr
pub fn get_binders<'a>(expr: &'a Expr, depth: Option<usize>) -> (Vec<((Name, BinderInfo), Expr)>, &'a Expr) {

  let mut ret = Vec::new();
  let mut expr = expr;
  let mut curr_depth = 0;

  loop {
    if let Some(d) = depth { if curr_depth == d { break } }
    match &expr {
      Expr::Pi(name, bi, typ, rem_expr) => {
        ret.push(((name.clone(), *bi), *typ.clone()));
        expr = rem_expr;
      },
      _ => break
    }

    curr_depth = curr_depth + 1;
  }

  (ret, expr)
}

// This feels slightly hacky
pub fn with_binders(var: String, bi: &BinderInfo) -> String {
  match bi {
    BinderInfo::Default => format!("({})", var),
    BinderInfo::Implicit => format!("{{{}}}", var),
    BinderInfo::InstImplicit => format!("[{}]", var),
    BinderInfo::StrictImplicit => format!("{{{{{}}}}}", var),
  }
}
