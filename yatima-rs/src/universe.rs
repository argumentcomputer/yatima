use crate::{
  environment::{
    Env,
    EnvError,
    UnivAnonCid,
    UnivCid,
    UnivMetaCid,
  },
  name::Name,
  nat::Nat,
};

use serde::{
  Deserialize,
  Serialize,
};

use libipld::serde::to_ipld;

use alloc::fmt;
use multihash::{
  Code,
  MultihashDigest,
};

use libipld::{
  cbor::DagCborCodec,
  codec::Codec,
};

/// Universe levels
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Univ {
  /// Sort 0 aka Prop
  Zero,
  /// Sort (n + 1)
  Succ(Box<Univ>),
  /// Sort (max u v)
  Max(Box<Univ>, Box<Univ>),
  /// Sort (imax u v)
  IMax(Box<Univ>, Box<Univ>),
  /// Sort u
  Param(Name, Nat),
}

impl Univ {
  pub fn cid(&self, env: &mut Env) -> Result<UnivCid, EnvError> {
    match self {
      Univ::Zero => {
        let anon = UnivAnon::Zero.store(env)?;
        let meta = UnivMeta::Zero.store(env)?;
        Ok(UnivCid { anon, meta })
      }
      Univ::Succ(x) => {
        let x_cid = x.cid(env)?;
        let anon = UnivAnon::Succ(x_cid.anon).store(env)?;
        let meta = UnivMeta::Succ(x_cid.meta).store(env)?;
        Ok(UnivCid { anon, meta })
      }
      Univ::Max(l, r) => {
        let l_cid = l.cid(env)?;
        let r_cid = r.cid(env)?;
        let anon = UnivAnon::Max(l_cid.anon, r_cid.anon).store(env)?;
        let meta = UnivMeta::Max(l_cid.meta, r_cid.meta).store(env)?;
        Ok(UnivCid { anon, meta })
      }
      Univ::IMax(l, r) => {
        let l_cid = l.cid(env)?;
        let r_cid = r.cid(env)?;
        let anon = UnivAnon::IMax(l_cid.anon, r_cid.anon).store(env)?;
        let meta = UnivMeta::IMax(l_cid.meta, r_cid.meta).store(env)?;
        Ok(UnivCid { anon, meta })
      }
      Univ::Param(name, idx) => {
        let anon = UnivAnon::Param(idx.clone()).store(env)?;
        let meta = UnivMeta::Param(name.clone()).store(env)?;
        Ok(UnivCid { anon, meta })
      }
    }
  }

  pub fn store(self, env: &mut Env) -> Result<UnivCid, EnvError> {
    let cid = self.cid(env)?;
    env.insert_univ_cache(cid, self);
    Ok(cid)
  }

  pub fn pretty(&self, ind: bool) -> String {
    fn succs(x: &Univ, count: usize, ind: bool) -> String {
      match x {
        Univ::Succ(p) => succs(p, count + 1, ind),
        Univ::Zero => format!("{}", count),
        x => format!("({} + {})", x.pretty(ind), count),
      }
    }
    match self {
      Univ::Zero => format!("0"),
      Univ::Param(n, i) if ind => format!("{}^{}", n, i),
      Univ::Param(n, _) => format!("{}", n),
      Univ::Succ(p) => succs(p, 1, ind),
      Univ::IMax(l, r) => format!("(imax {} {})", l.pretty(ind), r.pretty(ind)),
      Univ::Max(l, r) => format!("(max {} {})", l.pretty(ind), r.pretty(ind)),
    }
  }
}

impl fmt::Display for Univ {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.pretty(false))
  }
}

/// IPLD Serialization:
/// UnivMeta::Zero => [0]
/// UnivMeta::Succ => [1, <pred_cid>]
/// UnivMeta::Max => [2, <lhs_cid>, <rhs_cid>]
/// UnivMeta::IMax => [3, <lhs_cid>, <rhs_cid>]
/// UnivMeta::Param => [4, <name>]
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum UnivMeta {
  Zero,
  Succ(UnivMetaCid),
  Max(UnivMetaCid, UnivMetaCid),
  IMax(UnivMetaCid, UnivMetaCid),
  Param(Name),
}

impl UnivMeta {
  pub fn cid(&self) -> Result<UnivMetaCid, EnvError> {
    let ipld = to_ipld(self).map_err(|e| EnvError::IpldError(e))?;
    let bytes =
      DagCborCodec.encode(&ipld).map_err(|e| EnvError::CborError(e))?;
    Ok(UnivMetaCid::new(Code::Sha3_256.digest(&bytes)))
  }

  pub fn store(self, env: &mut Env) -> Result<UnivMetaCid, EnvError> {
    let cid = self.cid()?;
    env.insert_univ_meta(cid, self);
    Ok(cid)
  }
}

/// IPLD Serialization:
/// UnivAnon::Zero => [0]
/// UnivAnon::Succ => [1, <pred_cid>]
/// UnivAnon::Max => [2, <lhs_cid>, <rhs_cid>]
/// UnivAnon::IMax => [3, <lhs_cid>, <rhs_cid>]
/// UnivAnon::Param => [4, <idx>]
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum UnivAnon {
  Zero,
  Succ(UnivAnonCid),
  Max(UnivAnonCid, UnivAnonCid),
  IMax(UnivAnonCid, UnivAnonCid),
  Param(Nat),
}

impl UnivAnon {
  pub fn cid(&self) -> Result<UnivAnonCid, EnvError> {
    let ipld = to_ipld(self).map_err(|e| EnvError::IpldError(e))?;
    let bytes =
      DagCborCodec.encode(&ipld).map_err(|e| EnvError::CborError(e))?;
    Ok(UnivAnonCid::new(Code::Sha3_256.digest(&bytes)))
  }

  pub fn store(self, env: &mut Env) -> Result<UnivAnonCid, EnvError> {
    let cid = self.cid()?;
    env.insert_univ_anon(cid, self);
    Ok(cid)
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use crate::test::frequency;
  use im::Vector;
  use quickcheck::{
    Arbitrary,
    Gen,
  };
  
  use crate::parse::utils::UnivCtx;

  pub fn dummy_univ_ctx() -> UnivCtx {
    Vector::from(vec![Name::from("w"), Name::from("v"), Name::from("u")])
  }

  pub fn arbitrary_univ(g: &mut Gen, univ_ctx: &UnivCtx) -> Univ {
    let input: Vec<(usize, Box<dyn Fn(&mut Gen) -> Univ>)> = vec![
      (100, Box::new(|_| Univ::Zero)),
      (100,
        Box::new(|g| {
          if univ_ctx.len() > 0 {
            let i = usize::arbitrary(g) % univ_ctx.len();
            let n = &univ_ctx[i];
            Univ::Param(n.clone(), i.into())
          }
          else {
            Univ::Zero
          }
        }),
      ),
      (g.size().saturating_sub(30), Box::new(|g| Univ::Succ(Box::new(arbitrary_univ(g, univ_ctx))))),
      (g.size().saturating_sub(40),
        Box::new(|g| {
          Univ::Max(
            Box::new(arbitrary_univ(g, univ_ctx)),
            Box::new(arbitrary_univ(g, univ_ctx)),
          )
        }),
      ),
      (g.size().saturating_sub(40),
        Box::new(|g| {
          Univ::IMax(
            Box::new(arbitrary_univ(g, univ_ctx)),
            Box::new(arbitrary_univ(g, univ_ctx)),
          )
        }),
      ),
    ];
    frequency(g, input)
  }

  impl Arbitrary for Univ {
    fn arbitrary(g: &mut Gen) -> Self {
      arbitrary_univ(g, &dummy_univ_ctx())
    }
  }

  #[test]
  fn test_print_univ() {
    fn test(x: Univ, i: &str) { assert_eq!(x.pretty(true), String::from(i)) }
    test(Univ::Zero, "0");
    test(Univ::Succ(Box::new(Univ::Zero)), "1");
    test(
      Univ::Succ(Box::new(Univ::Param(Name::from("u"), 0u64.into()))),
      "(u^0 + 1)",
    );
    test(
      Univ::IMax(
        Box::new(Univ::Param(Name::from("u"), 0u64.into())),
        Box::new(Univ::Param(Name::from("v"), 1u64.into())),
      ),
      "(imax u^0 v^1)",
    );
    test(
      Univ::Max(
        Box::new(Univ::Param(Name::from("u"), 0u64.into())),
        Box::new(Univ::Param(Name::from("v"), 1u64.into())),
      ),
      "(max u^0 v^1)",
    );
  }
}
