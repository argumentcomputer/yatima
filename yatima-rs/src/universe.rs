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
    env.insert_univ(cid, self)?;
    Ok(cid)
  }
}

/// IPLD Serialization:
/// UnivMeta::Zero => [0]
/// UnivMeta::Succ => [1, <pred_cid>]
/// UnivMeta::Max => [2, <lhs_cid>, <rhs_cid>]
/// UnivMeta::IMax => [3, <lhs_cid>, <rhs_cid>]
/// UnivMeta::Param => [4, <name>]
#[derive(Clone, Debug, Serialize, Deserialize)]
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
    env.insert_univ_meta(cid, self)?;
    Ok(cid)
  }
}

/// IPLD Serialization:
/// UnivAnon::Zero => [0]
/// UnivAnon::Succ => [1, <pred_cid>]
/// UnivAnon::Max => [2, <lhs_cid>, <rhs_cid>]
/// UnivAnon::IMax => [3, <lhs_cid>, <rhs_cid>]
/// UnivAnon::Param => [4, <idx>]
#[derive(Clone, Debug, Serialize, Deserialize)]
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
    env.insert_univ_anon(cid, self)?;
    Ok(cid)
  }
}
