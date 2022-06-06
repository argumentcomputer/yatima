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
  name::Name,
  expression::{
    Expr,
    BinderInfo,
  },
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

use alloc::{
  fmt,
  string::String,
};

use libipld::{
  cbor::DagCborCodec,
  codec::Codec,
};

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum DefSafety {
  Unsafe,
  Safe,
  Partial,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum QuotKind {
  Type,
  Ctor,
  Lift,
  Ind,
}

/// Yatima Constants
#[derive(Clone, Debug, PartialEq)]
pub enum Const {
  /// Axiom: unsafe? axiom <name> {lvl*} : <typ>
  Axiom {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprCid,
    safe: bool
  },
  /// Theorem: theorem <name> {lvl*} : <typ> := <expr>
  Theorem {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprCid,
    expr: ExprCid
  },
  /// Opaque: unsafe? opaque rec? <name> {lvl*} : <typ> := <expr>
  Opaque {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprCid,
    expr: ExprCid,
    safe: bool
  },
  /// Definitions: unsafe? def rec? <name> {lvl*} : <typ> := <expr>
  Definition {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprCid,
    expr: ExprCid,
    safe: DefSafety,
  },
  /// Inductive Type:
  /// ```lean
  /// unsafe? inductive rec? <name> {lvl*} (<params>{num_params}) : <typ> where
  /// | constructor₁ : <expr>
  /// | ..
  /// | constructor₀ : <expr>
  /// ```
  /// wtf are nest and refl?
  Inductive {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprCid,
    params: usize,
    indices: usize,
    ctors: Vec<(Name, ExprCid)>,
    recr: bool,
    safe: bool,
    refl: bool,
    nest: bool,
  },
  /// Inductive constructor: ???
  Constructor {
    name: Name,
    lvl: Vec<Name>,
    ind: ConstCid,
    typ: ExprCid,
    param: Nat,
    field: Nat,
    safe: bool,
  },
  /// Inductive recursor
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

/// The input `Vector : ∀ (A: Type) -> ∀ (n: Nat) -> Sort 0` with depth 1 returns:
///   - string: `(A: Type)` 
///   - type: `∀ (n: Nat) -> Sort 0`
/// This is useful for printing defs
/// sort of the inverse of parse_bound_expressions?
/// Note that this doesn't fail -- it just stops parsing if it hits a non-pi expr
fn get_binders<'a>(expr: &'a Expr, env: &Env, ind: bool) -> (Vec<String>, &'a Expr) {
  // This feels slightly hacky
  fn with_binders(var: String, bi: &BinderInfo) -> String {
    match bi {
      BinderInfo::Default => format!("({})", var),
      BinderInfo::Implicit => format!("{{{}}}", var),
      BinderInfo::InstImplicit => format!("[{}]", var),
      BinderInfo::StrictImplicit => format!("{{{{{}}}}}", var),
    }
  }

  let mut ret = Vec::new();
  let mut expr = expr;

  loop {
    match expr {
      Expr::Pi(name, bi, typ, rem_expr) => {
        let bdd_var = with_binders(format!("{name} : {}", typ.pretty(env, ind)), bi);
        ret.push(bdd_var);
        expr = rem_expr;
      },
      _ => break
    }
  }

  (ret, expr)
}

impl Const {
  pub fn cid(&self, env: &mut Env) -> Result<ConstCid, EnvError> {
    match self {
      Const::Axiom { name, lvl, typ, safe } => {
        let anon =
          ConstAnon::Axiom {
            lvl: lvl.len().into(),
            typ: typ.anon,
            safe: *safe
          }.store(env)?;
        let meta = ConstMeta::Axiom{
          name: name.clone(),
          lvl: lvl.clone(),
          typ: typ.meta,
        }.store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Theorem { name, lvl, typ, expr } => {
        let anon =
          ConstAnon::Theorem{
            lvl: lvl.len().into(),
            typ: typ.anon,
            expr: expr.anon
          }.store(env)?;
        let meta = ConstMeta::Theorem{
          name: name.clone(),
          lvl: lvl.clone(),
          typ: typ.meta,
          expr: expr.meta,
        }.store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Opaque { name, lvl, typ, expr, safe } => {
        let anon = ConstAnon::Opaque{
          lvl: lvl.len().into(),
          typ: typ.anon,
          expr: expr.anon,
          safe: *safe,
        }.store(env)?;
        let meta = ConstMeta::Opaque{
          name: name.clone(),
          lvl: lvl.clone(),
          typ: typ.meta,
          expr: expr.meta,
        }.store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Definition { name, lvl, typ, expr, safe } => {
        let anon = ConstAnon::Definition{
          lvl: lvl.len().into(),
          typ: typ.anon,
          expr: expr.anon,
          safe: *safe,
        }.store(env)?;
        let meta = ConstMeta::Definition{
          name: name.clone(),
          lvl: lvl.clone(),
          typ: typ.meta,
          expr: expr.meta,
        }.store(env)?;
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
        let ctors_meta = ctors.iter().map(|(_, x)| x.meta.clone()).collect();
        let ctors_anon =
          ctors.iter().map(|(n, x)| (n.clone(), x.anon.clone())).collect();
        let anon = ConstAnon::Inductive{
          lvl: lvl.len().into(),
          typ: typ.anon,
          params: *params,
          indices: *indices,
          ctors: ctors_anon,
          recr: *recr,
          safe: *safe,
          refl: *refl,
          nest: *nest,
        }.store(env)?;
        let meta =
          ConstMeta::Inductive{
            name: name.clone(),
            lvl: lvl.clone(),
            typ: typ.meta,
            ctors: ctors_meta
          }.store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Constructor { name, lvl, ind, typ, param, field, safe } => {
        let anon = ConstAnon::Constructor{
          name: name.clone(),
          lvl: lvl.len().into(),
          ind: ind.anon,
          typ: typ.anon,
          param: param.clone(),
          field: field.clone(),
          safe: *safe,
        }.store(env)?;
        let meta = ConstMeta::Constructor{
          lvl: lvl.clone(),
          ind: ind.meta,
          typ: typ.meta,
        }.store(env)?;
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
        let anon = ConstAnon::Recursor{
          lvl: lvl.len().into(),
          ind: ind.anon,
          typ: typ.anon,
          params: params.clone(),
          indices: indices.clone(),
          motives: motives.clone(),
          minors: minors.clone(),
          rules: rules_anon,
          k: *k,
          safe: *safe,
        }.store(env)?;
        let meta =
          ConstMeta::Recursor{
            lvl: lvl.clone(),
            ind: ind.meta,
            typ: typ.meta,
            rules: rules_meta
          }.store(env)?;
        Ok(ConstCid { anon, meta })
      }
      Const::Quotient { kind } => {
        let anon = ConstAnon::Quotient{ kind: *kind }.store(env)?;
        let meta = ConstMeta::Quotient.store(env)?;
        Ok(ConstCid { anon, meta })
      }
    }
  }

  pub fn store(self, env: &mut Env) -> Result<ConstCid, EnvError> {
    let cid = self.cid(env)?;
    env.insert_const_cache(cid, self);
    Ok(cid)
  }

  pub fn pretty(self, ind: bool, env: &Env) -> Option<String> {
    fn pretty_lvls(lvl: Vec<Name>) -> String {
      lvl.iter()
         .map(|level| level.to_string())
         .collect::<Vec<String>>()
         .join(" ")
    }

    fn print_constructors(ind: bool, env: &Env, ctors: Vec<(Name, ExprCid)>) -> Option<String> {
      let ctors: Vec<_> = 
        ctors.into_iter()
             .map(|(name, expr_cid)| match env.expr_cache.get(&expr_cid) {
               Some(expr) => Some((name, expr)),
               None => None
             })
             .collect::<Option<Vec<_>>>()?;
      let res = 
        ctors.into_iter()
             .map(|(name, expr)| {
              let (bds, typ) = get_binders(expr, env, ind);
              format!("| {} {} : {},\n", name, bds.join(" "), typ.pretty(env, ind))
             })
             .collect::<Vec<String>>()
             .join("");
      Some(res)
    }

    match self {
      // Axiom: unsafe? axiom <name> {lvl*} : <typ>
      // TODO: (please help) make the code cleaner 
      Const::Axiom { name, lvl, typ, safe } => {
        let typ = env.expr_cache.get(&typ)?; 
        Some(format!("{} axiom {} {{{}}} : {}", 
                      safe, 
                      name, 
                      pretty_lvls(lvl), 
                      typ.pretty(env, ind)))
      }
      // Theorem: theorem <name> {lvl*} : <typ> := <expr>
      Const::Theorem { name, lvl, typ, expr } => {
        let typ = env.expr_cache.get(&typ)?; 
        let expr = env.expr_cache.get(&expr)?; 
        Some(format!("theorem {} {{{}}} : {} := {}", 
                      name, 
                      pretty_lvls(lvl), 
                      typ.pretty(env, ind),
                      expr.pretty(env, ind)))
      }
      // Opaque: unsafe? opaque rec? <name> {lvl*} : <typ> := <expr>
      Const::Opaque { name, lvl, typ, expr, safe } => {
        Some("".to_string())
      }
      Const::Definition { name, lvl, typ, expr, safe } => {
        Some("".to_string())
      }
      // Inductive Type:
      // ```lean
      // unsafe? inductive rec? <name> {lvl*} (<params>{num_params}) : <typ> where
      // | constructor₁ : <expr>
      // | ...
      // | constructor₀ : <expr>
      // ```
      Const::Inductive {
        name, lvl, typ, params, indices, 
        ctors, recr, safe, refl, nest,
      } => {
        let typ = env.expr_cache.get(&typ)?; 
        // here `<typ>` looks like `<params> -> <indices> -> <name>`
        // we need to unwrap the `<params>`
        let (bds, sort) = get_binders(typ, env, ind);
        let ctors_str = print_constructors(ind, env, ctors)?;
        Some(format!("{} inductive {} {} {{{}}} {} : {} -> {} where\n{}",
                      safe, 
                      recr,
                      name,
                      pretty_lvls(lvl),
                      bds[0..params].join(" "), // print params
                      bds[params..].join(" "), // print indices
                      sort.pretty(env, ind),
                      ctors_str)) // print ctors
      }
      Const::Constructor { name, lvl, ind, typ, param, field, safe } => {
        // TODO
        let typ = env.expr_cache.get(&typ)?;  
        let ind = env.const_cache.get(&ind)?;  
        Some(format!("| {}  ", name))
      }
      Const::Recursor { // TODO
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
        Some("".to_string())
      }
      Const::Quotient { kind } => {
        // TODO
        Some("".to_string())
      }
    }
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
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum ConstMeta {
  Axiom {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprMetaCid
  },
  Theorem {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprMetaCid,
    expr: ExprMetaCid
  },
  Opaque {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprMetaCid,
    expr: ExprMetaCid,
  },
  Definition {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprMetaCid,
    expr: ExprMetaCid,
  },
  Inductive {
    name: Name,
    lvl: Vec<Name>,
    typ: ExprMetaCid,
    ctors: Vec<ExprMetaCid>,
  },
  Constructor {
    lvl: Vec<Name>,
    ind: ConstMetaCid,
    typ: ExprMetaCid,
  },
  Recursor {
    lvl: Vec<Name>,
    ind: ConstMetaCid,
    typ: ExprMetaCid,
    rules: Vec<(ConstMetaCid, ExprMetaCid)>,
  },
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
    env.insert_const_meta(cid, self);
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
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum ConstAnon {
  Axiom {
    lvl: Nat,
    typ: ExprAnonCid,
    safe: bool
  },
  Theorem {
    lvl: Nat,
    typ: ExprAnonCid,
    expr: ExprAnonCid
  },
  Opaque {
    lvl: Nat,
    typ: ExprAnonCid,
    expr: ExprAnonCid,
    safe: bool,
  },
  Definition {
    lvl: Nat,
    typ: ExprAnonCid,
    expr: ExprAnonCid,
    safe: DefSafety,
  },
  Inductive {
    lvl: Nat,
    typ: ExprAnonCid,
    params: usize,
    indices: usize,
    ctors: Vec<(Name, ExprAnonCid)>,
    recr: bool,
    safe: bool,
    refl: bool,
    nest: bool,
  },
  Constructor {
    name: Name,
    lvl: Nat,
    ind: ConstAnonCid,
    typ: ExprAnonCid,
    param: Nat,
    field: Nat,
    safe: bool,
  },
  Recursor {
    lvl: Nat,
    ind: ConstAnonCid,
    typ: ExprAnonCid,
    params: Nat,
    indices: Nat,
    motives: Nat,
    minors: Nat,
    rules: Vec<(ConstAnonCid, Nat, ExprAnonCid)>,
    k: bool,
    safe: bool,
  },
  Quotient { kind: QuotKind },
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
    env.insert_const_anon(cid, self);
    Ok(cid)
  }
}
