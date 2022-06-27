use std::{
  borrow::Borrow,
  fmt,
  ops::Deref,
  rc::Rc,
};

use serde::{
  Deserialize,
  Serialize,
};

use alloc::string::{
  String,
  ToString,
};

/// The name for packages, defs, and expressions
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Name {
  inner: Rc<str>,
}
impl fmt::Debug for Name {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "\"{}\"", self.inner)
  }
}

impl AsRef<str> for Name {
  fn as_ref(&self) -> &str { self.inner.as_ref() }
}

impl Borrow<str> for Name {
  fn borrow(&self) -> &str { self.inner.borrow() }
}

impl fmt::Display for Name {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.inner.to_string())
  }
}

impl Deref for Name {
  type Target = str;

  fn deref(&self) -> &str { self.inner.deref() }
}

impl<'a> From<&'a str> for Name {
  fn from(v: &str) -> Name { Self { inner: Rc::from(v) } }
}

impl From<String> for Name {
  fn from(v: String) -> Name { Self { inner: Rc::from(v) } }
}

impl Serialize for Name {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where S: serde::Serializer {
    let string = self.inner.to_owned();
    string.serialize(serializer)
  }
}

impl<'de> Deserialize<'de> for Name {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where D: serde::Deserializer<'de> {
    let string = String::deserialize(deserializer)?;
    Ok(Name { inner: Rc::from(string.as_str()) })
  }
}

#[cfg(test)]
pub mod tests {

  use super::*;
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use crate::parse::utils::reserved_symbols;

  pub fn arbitrary_ascii_name(g: &mut Gen, len: usize) -> Name {
    let mut s: String;
    
    loop {
      s = String::new();
      while s.len() < len {
        let i = (u32::arbitrary(g) % 26) + 97;
        let c = unsafe { char::from_u32_unchecked(i) };
        s.push(c)
      }
      if !reserved_symbols().contains(&s) {
        break;
      }
    }

    Name::from(format!("{}", s))
  }
}
