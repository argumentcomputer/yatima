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
    UnivAnonCid,
    UnivMetaCid,
  },
  name::Name,
  nat::Nat,
  universe::Univ,
};
use serde::{
  Deserialize,
  Serialize,
};

use alloc::{
  boxed::Box,
  string::String,
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Literal {
  Nat(Nat),
  Str(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LitType {
  Nat,
  Str,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinderInfo {
  Default,
  Implicit,
  StrictImplict,
  InstImplict,
}

/// Yatima Expressions
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Expr {
  /// Variables
  Var(Name, Nat),
  /// Type Universes
  Sort(Univ),
  /// Global references to a Constant, with universe arguments
  Const(Name, ConstCid, Vec<Univ>),
  /// Function Application: (f x)
  App(Box<Expr>, Box<Expr>),
  /// Anonymous Function: λ (x : A) => x
  Lam(Name, BinderInfo, Box<Expr>, Box<Expr>),
  /// Universal Quantification: Π (x : A) -> x
  Pi(Name, BinderInfo, Box<Expr>, Box<Expr>),
  /// Local definition: let x : A = e in b
  Let(Name, Box<Expr>, Box<Expr>, Box<Expr>),
  /// Literal: "foo", 1, 2, 3
  Lit(Literal),
  /// Literal Type: Nat, String
  Lty(LitType),
  /// Fixpoint recursion, μ x. x
  Fix(Name, Box<Expr>),
}

impl Expr {
  pub fn cid(&self, env: &mut Env) -> Result<ExprCid, EnvError> {
    match self {
      Expr::Var(name, idx) => {
        let anon = ExprAnon::Var(idx.clone()).store(env)?;
        let meta = ExprMeta::Var(name.clone()).store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::Sort(univ) => {
        let univ_cid = univ.clone().store(env)?;
        let anon = ExprAnon::Sort(univ_cid.anon).store(env)?;
        let meta = ExprMeta::Sort(univ_cid.meta).store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::Const(name, const_cid, univs) => {
        let mut univ_anons = Vec::new();
        let mut univ_metas = Vec::new();
        for u in univs {
          let cid = u.clone().store(env)?;
          univ_anons.push(cid.anon);
          univ_metas.push(cid.meta);
        }
        let anon = ExprAnon::Const(const_cid.anon, univ_anons).store(env)?;
        let meta = ExprMeta::Const(name.clone(), const_cid.meta, univ_metas)
          .store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::App(fun, arg) => {
        let fun_cid = fun.cid(env)?;
        let arg_cid = arg.cid(env)?;
        let anon = ExprAnon::App(fun_cid.anon, arg_cid.anon).store(env)?;
        let meta = ExprMeta::App(fun_cid.meta, arg_cid.meta).store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::Lam(name, bind, typ, bod) => {
        let typ_cid = typ.cid(env)?;
        let bod_cid = bod.cid(env)?;
        let anon =
          ExprAnon::Lam(bind.clone(), typ_cid.anon, bod_cid.anon).store(env)?;
        let meta =
          ExprMeta::Lam(name.clone(), typ_cid.meta, bod_cid.meta).store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::Pi(name, bind, typ, bod) => {
        let typ_cid = typ.cid(env)?;
        let bod_cid = bod.cid(env)?;
        let anon =
          ExprAnon::Pi(bind.clone(), typ_cid.anon, bod_cid.anon).store(env)?;
        let meta =
          ExprMeta::Pi(name.clone(), typ_cid.meta, bod_cid.meta).store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::Let(name, typ, exp, bod) => {
        let typ_cid = typ.cid(env)?;
        let exp_cid = exp.cid(env)?;
        let bod_cid = bod.cid(env)?;
        let anon =
          ExprAnon::Let(typ_cid.anon, exp_cid.anon, bod_cid.anon).store(env)?;
        let meta =
          ExprMeta::Let(name.clone(), typ_cid.meta, exp_cid.meta, bod_cid.meta)
            .store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::Lit(x) => {
        let anon = ExprAnon::Lit(x.clone()).store(env)?;
        let meta = ExprMeta::Lit.store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::Lty(x) => {
        let anon = ExprAnon::Lty(x.clone()).store(env)?;
        let meta = ExprMeta::Lty.store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::Fix(name, x) => {
        let x_cid = x.cid(env)?;
        let anon = ExprAnon::Fix(x_cid.anon).store(env)?;
        let meta = ExprMeta::Fix(name.clone(), x_cid.meta).store(env)?;
        Ok(ExprCid { anon, meta })
      }
    }
  }

  pub fn store(self, env: &mut Env) -> Result<ExprCid, EnvError> {
    let cid = self.cid(env)?;
    env.insert_expr(cid, self)?;
    Ok(cid)
  }
}

/// IPLD Serialization:
/// ExprMeta::Var => [0, <name>]
/// ExprMeta::Sort => [1, <pred>]
/// ExprMeta::Const => [2, <name>, <const>, [<univs>*]]
/// ExprMeta::App => [3, <fun>, <arg>]
/// ExprMeta::Lam => [4, <name>, <type>, <body> ]
/// ExprMeta::Pi => [5, <name>, <type>, <body> ]
/// ExprMeta::Let => [6, <name>, <type>, <expr>, <body>]
/// ExprMeta::Lit => [7]
/// ExprMeta::Lty => [8]
/// ExprMeta::Fix => [9, <name>, <body>]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ExprMeta {
  Var(Name),
  Sort(UnivMetaCid),
  Const(Name, ConstMetaCid, Vec<UnivMetaCid>),
  App(ExprMetaCid, ExprMetaCid),
  Lam(Name, ExprMetaCid, ExprMetaCid),
  Pi(Name, ExprMetaCid, ExprMetaCid),
  Let(Name, ExprMetaCid, ExprMetaCid, ExprMetaCid),
  Lit,
  Lty,
  Fix(Name, ExprMetaCid),
}

impl ExprMeta {
  pub fn cid(&self) -> Result<ExprMetaCid, EnvError> {
    let ipld = to_ipld(self).map_err(|e| EnvError::IpldError(e))?;
    let bytes =
      DagCborCodec.encode(&ipld).map_err(|e| EnvError::CborError(e))?;
    Ok(ExprMetaCid::new(Code::Sha3_256.digest(&bytes)))
  }

  pub fn store(self, env: &mut Env) -> Result<ExprMetaCid, EnvError> {
    let cid = self.cid()?;
    env.insert_expr_meta(cid, self)?;
    Ok(cid)
  }
}

/// IPLD Serialization:
/// ExprAnon::Var => [0, <idx>]
/// ExprAnon::Sort => [1, <pred>]
/// ExprAnon::Const => [2, <const>, [<univs>*]]
/// ExprAnon::App => [3, <fun>, <arg>]
/// ExprAnon::Lam => [4, <bind>, <type>, <body> ]
/// ExprAnon::Pi => [5, <bind>, <type>, <body> ]
/// ExprAnon::Let => [6, <type>, <expr>, <body>]
/// ExprAnon::Lit => [7, <lit>]
/// ExprAnon::Lty => [8, <lty>]
/// ExprAnon::Fix => [9, <body>]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ExprAnon {
  Var(Nat),
  Sort(UnivAnonCid),
  Const(ConstAnonCid, Vec<UnivAnonCid>),
  App(ExprAnonCid, ExprAnonCid),
  Lam(BinderInfo, ExprAnonCid, ExprAnonCid),
  Pi(BinderInfo, ExprAnonCid, ExprAnonCid),
  Let(ExprAnonCid, ExprAnonCid, ExprAnonCid),
  Lit(Literal),
  Lty(LitType),
  Fix(ExprAnonCid),
}

impl ExprAnon {
  pub fn cid(&self) -> Result<ExprAnonCid, EnvError> {
    let ipld = to_ipld(self).map_err(|e| EnvError::IpldError(e))?;
    let bytes =
      DagCborCodec.encode(&ipld).map_err(|e| EnvError::CborError(e))?;
    Ok(ExprAnonCid::new(Code::Sha3_256.digest(&bytes)))
  }

  pub fn store(self, env: &mut Env) -> Result<ExprAnonCid, EnvError> {
    let cid = self.cid()?;
    env.insert_expr_anon(cid, self)?;
    Ok(cid)
  }
}

//#[cfg(test)]
// pub mod tests {
//  use crate::content::tests::frequency;
//
//  use super::*;
//  use quickcheck::{
//    Arbitrary,
//    Gen,
//  };
//
//  impl Arbitrary for Bind {
//    fn arbitrary(g: &mut Gen) -> Self {
//      let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Bind>)> = vec![
//        (1, Box::new(|_| Bind::Default)),
//        (1, Box::new(|_| Bind::Implicit)),
//        (1, Box::new(|_| Bind::Strict)),
//        (1, Box::new(|_| Bind::Class)),
//      ];
//      frequency(g, input)
//    }
//  }
//}
