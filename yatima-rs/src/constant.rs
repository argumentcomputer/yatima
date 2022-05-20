use crate::{
  environment::{
    ConstAnonCid,
    ConstCid,
    ConstMetaCid,
    Env,
    EnvError,
    ExprAnonCid,
    ExprCid,
    ExprMetaCid,
  },
  expression::Expr,
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

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum DefSafety {
  Unsafe,
  Safe,
  Partial,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum QuotKind {
  Type,
  Ctor,
  Lift,
  Ind,
}

/// Yatima Constants
#[derive(Clone, Debug)]
pub enum Const {
  /// axiom
  Axiom { name: Name, lvl: Vec<Name>, typ: ExprCid, safe: bool },
  /// theorem
  Theorem { name: Name, lvl: Vec<Name>, typ: ExprCid, expr: ExprCid },
  /// opaque
  Opaque { name: Name, lvl: Vec<Name>, typ: ExprCid, expr: ExprCid, safe: bool },
  /// def
  Definition {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprCid,
    expr: ExprCid,
    safe: DefSafety,
  },
  /// inductive type
  Inductive {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprCid,
    params: Nat,
    indices: Nat,
    ctors: Vec<(Name, ExprCid)>,
    recr: bool,
    safe: bool,
    refl: bool,
    nest: bool,
  },
  /// inductive constructor
  Constructor {
    name: Name,
    lvl: Vec<Name>,
    ind: ConstCid,
    typ: ExprCid,
    idx: Nat,
    param: Nat,
    field: Nat,
    safe: bool,
  },
  /// inductive recursor
  Recursor {
    lvl: Vec<Name>,
    ind: ConstCid,
    typ: ExprCid,
    params: Nat,
    indices: Nat,
    motives: Nat,
    minors: Nat,
    rules: Vec<(ConstCid, Nat, ExprCid)>,
    k: bool,
    safe: bool,
  },
  /// quotient
  Quotient { kind: QuotKind },
}

impl Const {
  pub fn cid(&self, env: &mut Env) -> Result<ConstCid, EnvError> {
    match self {
      Const::Axiom { name, lvl, typ, safe } => {
        let anon =
          ConstAnon::Axiom(lvl.len().into(), typ.anon, *safe).store(env)?;
        let meta =
          ConstMeta::Axiom(name.clone(), lvl.clone(), typ.meta).store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Theorem { name, lvl, typ, expr } => {
        let anon = ConstAnon::Theorem(lvl.len().into(), typ.anon, expr.anon)
          .store(env)?;
        let meta =
          ConstMeta::Theorem(name.clone(), lvl.clone(), typ.meta, expr.meta)
            .store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Opaque { name, lvl, typ, expr, safe } => {
        let anon =
          ConstAnon::Opaque(lvl.len().into(), typ.anon, expr.anon, *safe)
            .store(env)?;
        let meta =
          ConstMeta::Opaque(name.clone(), lvl.clone(), typ.meta, expr.meta)
            .store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Definition { name, lvl, typ, expr, safe } => {
        let anon =
          ConstAnon::Definition(lvl.len().into(), typ.anon, expr.anon, *safe)
            .store(env)?;
        let meta =
          ConstMeta::Definition(name.clone(), lvl.clone(), typ.meta, expr.meta)
            .store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Inductive {
        name,
        lvl,
        typ,
        params,
        indices,
        ctors,
        recr,
        safe,
        refl,
        nest,
      } => {
        let ctors_meta = ctors.iter().map(|(n, x)| x.meta.clone()).collect();
        let ctors_anon =
          ctors.iter().map(|(n, x)| (n.clone(), x.anon.clone())).collect();
        let anon = ConstAnon::Inductive(
          lvl.len().into(),
          typ.anon,
          params.clone(),
          indices.clone(),
          ctors_anon,
          *recr,
          *safe,
          *refl,
          *nest,
        )
        .store(env)?;
        let meta =
          ConstMeta::Inductive(name.clone(), lvl.clone(), typ.meta, ctors_meta)
            .store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Constructor { name, lvl, ind, typ, idx, param, field, safe } => {
        let anon = ConstAnon::Constructor(
          lvl.len().into(),
          ind.anon,
          typ.anon,
          idx.clone(),
          param.clone(),
          field.clone(),
          *safe,
        )
        .store(env)?;
        let meta =
          ConstMeta::Constructor(name.clone(), lvl.clone(), ind.meta, typ.meta)
            .store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Recursor {
        lvl,
        ind,
        typ,
        params,
        indices,
        motives,
        minors,
        rules,
        k,
        safe,
      } => {
        let mut rules_anon: Vec<(ConstAnonCid, Nat, ExprAnonCid)> = Vec::new();
        let mut rules_meta: Vec<(ConstMetaCid, ExprMetaCid)> = Vec::new();
        for (ctor_cid, fields, rhs) in rules {
          rules_anon.push((ctor_cid.anon, fields.clone(), rhs.anon));
          rules_meta.push((ctor_cid.meta, rhs.meta));
        }
        let anon = ConstAnon::Recursor(
          lvl.len().into(),
          ind.anon,
          typ.anon,
          params.clone(),
          indices.clone(),
          motives.clone(),
          minors.clone(),
          rules_anon,
          *k,
          *safe,
        )
        .store(env)?;
        let meta =
          ConstMeta::Recursor(lvl.clone(), ind.meta, typ.meta, rules_meta)
            .store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Quotient { kind } => {
        let anon = ConstAnon::Quotient(*kind).store(env)?;
        let meta = ConstMeta::Quotient.store(env)?;
        Ok(ConstCid { anon, meta })
      }
    }
  }

  pub fn store(self, env: &mut Env) -> Result<ConstCid, EnvError> {
    let cid = self.cid(env)?;
    env.insert_const(cid, self)?;
    Ok(cid)
  }
}

/// IPLD Serialization:
/// ConstMeta::Axiom => [0, <name>, [<name>*], <type>]
/// ConstMeta::Theorem => [1, <name>, [<name>*], <type>, <expr>]
/// ConstMeta::Opaque => [2, <name>, [<name>*], <type>, <expr>]
/// ConstMeta::Definition => [3, <name>, [<name>*], <type>, <expr>]
/// ConstMeta::Inductive  => [4, <name>, [<name>*], <type>, <expr>]
/// ConstMeta::Constructor  => [5, <name>, [<name>*], <const>, <type>]
/// ConstMeta::Recursor => [6, [<name>*], <const>, <type>, [<rules>*]]
/// ConstMeta::Quotient => [7]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ConstMeta {
  Axiom(Name, Vec<Name>, ExprMetaCid),
  Theorem(Name, Vec<Name>, ExprMetaCid, ExprMetaCid),
  Opaque(Name, Vec<Name>, ExprMetaCid, ExprMetaCid),
  Definition(Name, Vec<Name>, ExprMetaCid, ExprMetaCid),
  Inductive(Name, Vec<Name>, ExprMetaCid, Vec<ExprMetaCid>),
  Constructor(Name, Vec<Name>, ConstMetaCid, ExprMetaCid),
  Recursor(
    Vec<Name>,
    ConstMetaCid,
    ExprMetaCid,
    Vec<(ConstMetaCid, ExprMetaCid)>,
  ),
  Quotient,
}

impl ConstMeta {
  pub fn cid(&self) -> Result<ConstMetaCid, EnvError> {
    let ipld = to_ipld(self).map_err(|e| EnvError::IpldError(e))?;
    let bytes =
      DagCborCodec.encode(&ipld).map_err(|e| EnvError::CborError(e))?;
    Ok(ConstMetaCid::new(Code::Sha3_256.digest(&bytes)))
  }

  pub fn store(self, env: &mut Env) -> Result<ConstMetaCid, EnvError> {
    let cid = self.cid()?;
    env.insert_const_meta(cid, self)?;
    Ok(cid)
  }
}

/// IPLD Serialization:
/// ConstAnon::Axiom => [0, <lvls>, <type>]
/// ConstAnon::Theorem => [1, <lvls>, <type>, <expr>]
/// ConstAnon::Opaque => [2, <lvls>, <type>, <expr>, <safe>]
/// ConstAnon::Definition => [3, <lvls>, <type>, <expr>, <safe>]
/// ConstAnon::Inductive  =>
///   [4, <lvls>, <type>, <params>, <indices>, <unit>
///   , <rec>, <safe>, <refl>, <nest>
///   ]
/// ConstAnon::Constructor  =>
///   [5, <lvls>, <ind>, <type>, <idx>, <params>, <fields>, <safe> ]
/// ConstAnon::Recursor =>
///   [6, <lvls>, <ind>, <type>, <params>, <indices>
///   , <motives>, <minors>, [<rules>*], <k>, <safe>
///   ]
/// ConstAnon::Quotient => [7, <kind>]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ConstAnon {
  Axiom(Nat, ExprAnonCid, bool),
  Theorem(Nat, ExprAnonCid, ExprAnonCid),
  Opaque(Nat, ExprAnonCid, ExprAnonCid, bool),
  Definition(Nat, ExprAnonCid, ExprAnonCid, DefSafety),
  Inductive(
    Nat,
    ExprAnonCid,
    Nat,
    Nat,
    Vec<(Name, ExprAnonCid)>,
    bool,
    bool,
    bool,
    bool,
  ),
  Constructor(Nat, ConstAnonCid, ExprAnonCid, Nat, Nat, Nat, bool),
  Recursor(
    Nat,
    ConstAnonCid,
    ExprAnonCid,
    Nat,
    Nat,
    Nat,
    Nat,
    Vec<(ConstAnonCid, Nat, ExprAnonCid)>,
    bool,
    bool,
  ),
  Quotient(QuotKind),
}

impl ConstAnon {
  pub fn cid(&self) -> Result<ConstAnonCid, EnvError> {
    let ipld = to_ipld(self).map_err(|e| EnvError::IpldError(e))?;
    let bytes =
      DagCborCodec.encode(&ipld).map_err(|e| EnvError::CborError(e))?;
    Ok(ConstAnonCid::new(Code::Sha3_256.digest(&bytes)))
  }

  pub fn store(self, env: &mut Env) -> Result<ConstAnonCid, EnvError> {
    let cid = self.cid()?;
    env.insert_const_anon(cid, self)?;
    Ok(cid)
  }
}
