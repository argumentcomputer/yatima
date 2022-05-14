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

use libipld::error::SerdeError;

use alloc::collections::{
  BTreeMap,
  BTreeSet,
};
use cid::Cid;
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

pub struct Env {
  pub univs: BTreeMap<UnivCid, Univ>,
  pub exprs: BTreeMap<ExprCid, Expr>,
  pub consts: BTreeMap<ConstCid, Const>,

  pub univ_meta: BTreeMap<UnivMetaCid, UnivMeta>,
  pub expr_meta: BTreeMap<ExprMetaCid, ExprMeta>,
  pub const_meta: BTreeMap<ConstMetaCid, ConstMeta>,

  pub univ_anon: BTreeMap<UnivAnonCid, UnivAnon>,
  pub expr_anon: BTreeMap<ExprAnonCid, ExprAnon>,
  pub const_anon: BTreeMap<ConstAnonCid, ConstAnon>,
}

pub enum EnvError {
  IpldError(SerdeError),
  CborError(libipld::error::Error),
  UnivMetaInsert,
  UnivAnonInsert,
  UnivInsert,
  ExprMetaInsert,
  ExprAnonInsert,
  ExprInsert,
  ConstMetaInsert,
  ConstAnonInsert,
  ConstInsert,
}

impl Env {
  pub fn insert_univ_anon(
    &mut self,
    k: UnivAnonCid,
    v: UnivAnon,
  ) -> Result<UnivAnon, EnvError> {
    self.univ_anon.insert(k, v).ok_or(EnvError::UnivAnonInsert)
  }

  pub fn insert_univ_meta(
    &mut self,
    k: UnivMetaCid,
    v: UnivMeta,
  ) -> Result<UnivMeta, EnvError> {
    self.univ_meta.insert(k, v).ok_or(EnvError::UnivMetaInsert)
  }

  pub fn insert_univ(&mut self, k: UnivCid, v: Univ) -> Result<Univ, EnvError> {
    self.univs.insert(k, v).ok_or(EnvError::UnivInsert)
  }

  pub fn insert_expr_anon(
    &mut self,
    k: ExprAnonCid,
    v: ExprAnon,
  ) -> Result<ExprAnon, EnvError> {
    self.expr_anon.insert(k, v).ok_or(EnvError::ExprAnonInsert)
  }

  pub fn insert_expr_meta(
    &mut self,
    k: ExprMetaCid,
    v: ExprMeta,
  ) -> Result<ExprMeta, EnvError> {
    self.expr_meta.insert(k, v).ok_or(EnvError::ExprMetaInsert)
  }

  pub fn insert_expr(&mut self, k: ExprCid, v: Expr) -> Result<Expr, EnvError> {
    self.exprs.insert(k, v).ok_or(EnvError::ExprInsert)
  }

  pub fn insert_const_anon(
    &mut self,
    k: ConstAnonCid,
    v: ConstAnon,
  ) -> Result<ConstAnon, EnvError> {
    self.const_anon.insert(k, v).ok_or(EnvError::ConstAnonInsert)
  }

  pub fn insert_const_meta(
    &mut self,
    k: ConstMetaCid,
    v: ConstMeta,
  ) -> Result<ConstMeta, EnvError> {
    self.const_meta.insert(k, v).ok_or(EnvError::ConstMetaInsert)
  }

  pub fn insert_const(
    &mut self,
    k: ConstCid,
    v: Const,
  ) -> Result<Const, EnvError> {
    self.consts.insert(k, v).ok_or(EnvError::ConstInsert)
  }
}

#[derive(
  Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct EnvSet {
  pub consts: BTreeSet<ConstCid>,
}
