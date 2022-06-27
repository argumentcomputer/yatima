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

use im::Vector;
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

/// The canonical form of an environment This is what
/// gets serialized/deserialized/hashed to form EnvCids.
#[derive(
  Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct EnvSet {
  pub env: BTreeSet<ConstCid>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct EnvNode {
  pub neighbours: Vec<ConstCid>,
  pub in_degree: usize,
}

impl EnvNode {
  pub fn new() -> Self {
    EnvNode {
      neighbours: Vec::<ConstCid>::new(),
      in_degree: 0,
    }
  }

  // pub fn get_neighbours(&self) -> &Vec<ConstCid> {
  //   self.neighbours
  // }
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

  pub const_dag: BTreeMap<ConstCid, EnvNode>,
  pub in_degree: BTreeMap<ConstCid, usize>,
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
      const_dag: BTreeMap::new(),
      in_degree: BTreeMap::new(),
    }
  }

  pub fn extend(&mut self, other: Self){
    self.const_cache.extend(other.const_cache);
    self.expr_cache.extend(other.expr_cache);
    self.univ_cache.extend(other.univ_cache);
    self.const_meta.extend(other.const_meta);
    self.expr_meta.extend(other.expr_meta);
    self.univ_meta.extend(other.univ_meta);
    self.const_anon.extend(other.const_anon);
    self.expr_anon.extend(other.expr_anon);
    self.univ_anon.extend(other.univ_anon);
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

  pub fn get_univ_cache(&self, k: &UnivCid) -> Option<&Univ> {
    self.univ_cache.get(k)
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

  fn make_dag(&self) -> BTreeMap<ConstCid, EnvNode> {
    let mut dag = BTreeMap::new();
    let mut in_degrees: BTreeMap<ConstCid, usize> = BTreeMap::new();
    // first clone the keys
    // we need to do this to have all the cids accessible when
    // we start counting the in-degrees of each node
    for (cid, const_decl) in &self.const_cache {
      let refs = const_decl.get_internal_refs(self);
      dag.insert(cid.clone(), EnvNode { neighbours: refs, in_degree: 0 });
      in_degrees.insert(*cid, 0);
    }

    for (_, node) in &dag {
      let neighbours = &node.neighbours;
      for n in neighbours {
        *in_degrees.get_mut(n).unwrap() += 1;
      }
    }

    for (cid, node) in &mut dag {
      node.in_degree = *in_degrees.get_mut(cid).unwrap();
    }

    // The three for loops are disturbing to me, 
    // but the problem is this: given an node A,
    // we must 1. get A's `neighbours`; 
    //         2. for each `neighbour` n, 
    //            increment `n.in_degree`.
    // However, Rust's borrow checker cannot guarantee 
    // that A is not equal to n, so it does not allow
    // the mutation of n while A is borrowed.
    // To amend this, I count all the in degrees
    // in a separate map, then copy over the values.

    return dag;
  }

  pub fn topo_sort(&self) -> Vector<ConstCid> {
    let mut const_dag = self.make_dag();
    let mut res = Vector::<ConstCid>::new();
    let mut s: Vector<ConstCid> = 
      const_dag.iter()
          .filter(|(_, x)| x.in_degree == 0)
          .map(|(x, _)| x)
          .cloned()
          .collect();
    while !s.is_empty() {
      let curr = s.pop_back().unwrap();
      res.push_back(curr);
      for n in const_dag.get(&curr).unwrap().neighbours.clone() {
        const_dag.get_mut(&n).unwrap().in_degree -= 1;
        if const_dag.get(&n).unwrap().in_degree == 0 {
          s.push_back(n);
        }
      }
    }
    res
  }

  /// Top level printer that will produce all the decls in an enviroment 
  pub fn pretty(&self, ind: bool) -> Option<String> {
    let cids = self.topo_sort();
    let res = cids.into_iter().map(|cid| {
      let decl = self.const_cache.get(&cid).unwrap();
      let pretty = decl.pretty(self, ind);
      pretty
    }).rev().collect::<Option<Vec<_>>>()?.join("\n\n");
    Some(res)
  } 
}

#[cfg(test)]
pub mod tests {
  use crate::name::tests::arbitrary_ascii_name;

  use crate::constant::tests::arbitrary_constenv;

  use im::OrdMap;

  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::*;

  
  impl Arbitrary for Env {
    fn arbitrary(g: &mut Gen) -> Env {
      let env_size = usize::arbitrary(g) % 10 + 1;

      let mut global_ctx = OrdMap::new();
      let mut env = Env::new();
      for _ in 0..env_size { 
        let mut name;
        loop {
          name = arbitrary_ascii_name(g, 5);
          if let None = global_ctx.get(&name) {
            break;
          }
        }
        let mut constenv = arbitrary_constenv(g, Some(name.clone()), &global_ctx);

        let cnstcid = constenv.cnst.store(&mut constenv.env).unwrap();
        global_ctx.insert(name.clone(), cnstcid);
        env.extend(constenv.env);
      }

      env
    }
  }
}
