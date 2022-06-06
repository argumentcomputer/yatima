use crate::{
  constant::{
    Const,
    ConstAnon,
    ConstMeta,
  },
  expression::{
    Expr,
    ExprAnon,
    ExprMeta,
  },
  universe::{
    Univ,
    UnivAnon,
    UnivMeta,
  },
};

use alloc::collections::{
  BTreeMap,
  BTreeSet,
};

use cid::Cid;
use libipld::error::SerdeError;
use multihash::Multihash;
use serde::{
  Deserialize,
  Serialize,
};

// Cid codec values, should be added to the Multicodec table
pub const UNIV_ANON: u64 = 0xC0DE0001;
pub const EXPR_ANON: u64 = 0xC0DE0002;
pub const CONST_ANON: u64 = 0xC0DE0003;
pub const UNIV_META: u64 = 0xC0DE0004;
pub const EXPR_META: u64 = 0xC0DE0005;
pub const CONST_META: u64 = 0xC0DE0006;

#[derive(
  Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct UnivAnonCid(pub Cid);

impl UnivAnonCid {
  pub fn new(hash: Multihash) -> Self {
    UnivAnonCid(Cid::new_v1(UNIV_ANON, hash))
  }
}

#[derive(
  Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct ExprAnonCid(pub Cid);

impl ExprAnonCid {
  pub fn new(hash: Multihash) -> Self {
    ExprAnonCid(Cid::new_v1(EXPR_ANON, hash))
  }
}

#[derive(
  Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct ConstAnonCid(pub Cid);

impl ConstAnonCid {
  pub fn new(hash: Multihash) -> Self {
    ConstAnonCid(Cid::new_v1(CONST_ANON, hash))
  }
}

#[derive(
  Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct UnivMetaCid(pub Cid);

impl UnivMetaCid {
  pub fn new(hash: Multihash) -> Self {
    UnivMetaCid(Cid::new_v1(UNIV_META, hash))
  }
}

#[derive(
  Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct ExprMetaCid(pub Cid);

impl ExprMetaCid {
  pub fn new(hash: Multihash) -> Self {
    ExprMetaCid(Cid::new_v1(EXPR_META, hash))
  }
}

#[derive(
  Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct ConstMetaCid(pub Cid);

impl ConstMetaCid {
  pub fn new(hash: Multihash) -> Self {
    ConstMetaCid(Cid::new_v1(CONST_META, hash))
  }
}

#[derive(
  Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct UnivCid {
  pub anon: UnivAnonCid,
  pub meta: UnivMetaCid,
}

#[derive(
  Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct ExprCid {
  pub anon: ExprAnonCid,
  pub meta: ExprMetaCid,
}

#[derive(
  Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct ConstCid {
  pub anon: ConstAnonCid,
  pub meta: ConstMetaCid,
}

/// The canonical form of an environment This is what
/// gets serialized/deserialized/hashed to form EnvCids.
#[derive(
  Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct EnvSet {
  pub env: BTreeSet<ConstCid>,
}

/// A Yatima Environment, which includes the full Merkle tree of all the various
/// CIDs, and also caches the Const/Expr/Univ trees to avoid frequent Anon/Meta
/// merges
#[derive(Clone, Debug, PartialEq)]
pub struct Env {
  /// The keys of the const_cache form the EnvSet
  pub const_cache: BTreeMap<ConstCid, Const>,
  pub expr_cache: BTreeMap<ExprCid, Expr>,
  pub univ_cache: BTreeMap<UnivCid, Univ>,

  pub const_meta: BTreeMap<ConstMetaCid, ConstMeta>,
  pub expr_meta: BTreeMap<ExprMetaCid, ExprMeta>,
  pub univ_meta: BTreeMap<UnivMetaCid, UnivMeta>,

  pub univ_anon: BTreeMap<UnivAnonCid, UnivAnon>,
  pub expr_anon: BTreeMap<ExprAnonCid, ExprAnon>,
  pub const_anon: BTreeMap<ConstAnonCid, ConstAnon>,
}

#[derive(Debug)]
pub enum EnvError {
  IpldError(SerdeError),
  CborError(libipld::error::Error),
}

impl Env {
  pub fn new() -> Self {
    Env {
      const_cache: BTreeMap::new(),
      expr_cache: BTreeMap::new(),
      univ_cache: BTreeMap::new(),
      const_meta: BTreeMap::new(),
      expr_meta: BTreeMap::new(),
      univ_meta: BTreeMap::new(),
      const_anon: BTreeMap::new(),
      expr_anon: BTreeMap::new(),
      univ_anon: BTreeMap::new(),
    }
  }

  pub fn insert_univ_anon(&mut self, k: UnivAnonCid, v: UnivAnon) {
    self.univ_anon.insert(k, v);
  }

  pub fn insert_univ_meta(&mut self, k: UnivMetaCid, v: UnivMeta) {
    self.univ_meta.insert(k, v);
  }

  pub fn insert_univ_cache(&mut self, k: UnivCid, v: Univ) {
    self.univ_cache.insert(k, v);
  }

  pub fn insert_expr_anon(&mut self, k: ExprAnonCid, v: ExprAnon) {
    self.expr_anon.insert(k, v);
  }

  pub fn insert_expr_meta(&mut self, k: ExprMetaCid, v: ExprMeta) {
    self.expr_meta.insert(k, v);
  }

  pub fn insert_expr_cache(&mut self, k: ExprCid, v: Expr) {
    self.expr_cache.insert(k, v);
  }

  pub fn insert_const_anon(&mut self, k: ConstAnonCid, v: ConstAnon) {
    self.const_anon.insert(k, v);
  }

  pub fn insert_const_meta(&mut self, k: ConstMetaCid, v: ConstMeta) {
    self.const_meta.insert(k, v);
  }

  pub fn insert_const_cache(&mut self, k: ConstCid, v: Const) {
    self.const_cache.insert(k, v);
  }
}
