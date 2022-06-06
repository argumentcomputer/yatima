use num_bigint::BigUint;

use crate::{
  name::{
    Name,
    NamePart,
  },
  parse::{
    base::{
      parse_litbase_digits,
      LitBase,
    },
    error::{
      ParseError,
      ParseErrorKind,
    },
    span::Span,
    utils::parse_integer,
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

// pub fn parse_text(from: Span) -> IResult<Span, String, ParseError<Span>> {
//  let (i, s) = take_till1(|x| char::is_whitespace(x) | (x == '.'))(from)?;
//  let s: String = String::from(s.fragment().to_owned());
//  Ok((i, s))
//}
