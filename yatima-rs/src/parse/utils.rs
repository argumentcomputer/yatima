use crate::parse::{
  base,
  error::{
    ParseError,
    ParseErrorKind,
  },
  span::Span,
};

use crate::{
  name::Name,
  nat::Nat,
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
  multi::many0,
  sequence::terminated,
  Err,
  IResult,
};

use alloc::string::String;

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
  let (i, s) = take_till1(|x| {
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
  })(from)?;
  let s: String = String::from(s.fragment().to_owned());
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
