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

use im::{
  Vector,
};

use multihash::{
  Code,
  MultihashDigest,
};

use alloc::{
  string::String,
};

use libipld::{
  cbor::DagCborCodec,
  codec::Codec,
};

use crate::parse::utils::{
  with_binders,
  get_binders,
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
    params: usize,
    indices: usize,
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

  pub fn name(&self) -> Name {
    match self {
      Const::Axiom { name, .. } => { name.clone() }
      Const::Theorem { name, .. } => { name.clone() }
      Const::Opaque { name, .. } => { name.clone() }
      Const::Definition { name, .. } => { name.clone() }
      Const::Inductive { name, .. } => { name.clone() }
      Const::Constructor { name, .. } => { name.clone() }
      Const::Recursor { .. } => { Name::from("") }
      Const::Quotient { .. } => { Name::from("") }
    }
  }

  pub fn store(self, env: &mut Env) -> Result<ConstCid, EnvError> {
    let cid = self.cid(env)?;
    env.insert_const_cache(cid, self);
    Ok(cid)
  }

  pub fn pretty(&self, env: &Env, ind: bool) -> Option<String> {
    fn pretty_lvls(lvl: &Vec<Name>) -> String {
      if lvl.len() > 0 { 
        let lvls_str = lvl.iter()
           .map(|level| level.to_string())
           .collect::<Vec<String>>()
           .join(" ");
        format!(" {{{}}}", lvls_str)
      } else { "".to_string() }
    }

    fn print_constructors(ind: bool, env: &Env, ctors: &Vec<(Name, ExprCid)>) -> Option<String> {
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
              let (bds, typ) = get_binders(expr, None);
              let bds: Vec<String> = bds.iter().map(|((n, bi), e)| with_binders(format!("{n} : {}", e.pretty(env, ind)), bi)).collect();
              format!("| {} {} : {},\n", name, bds.join(" "), typ.pretty(env, ind))
             })
             .collect::<Vec<String>>()
             .join("");
      Some(res)
    }

    match self {
      // Axiom: unsafe? axiom <name> {lvl*}? : <typ>
      // TODO: (please help) make the code cleaner 
      Const::Axiom { name, lvl, typ, safe } => {
        let typ = env.expr_cache.get(&typ)?; 
        let safety_str = if *safe { "" } else { "unsafe " };
        Some(format!("{}axiom {}{} : {}", 
                      safety_str, 
                      name, 
                      pretty_lvls(lvl), 
                      typ.pretty(env, ind)))
      }
      // Theorem: theorem <name> {lvl*}? : <typ> := <expr>
      Const::Theorem { name, lvl, typ, expr } => {
        let typ = env.expr_cache.get(&typ)?; 
        let expr = env.expr_cache.get(&expr)?; 
        Some(format!("theorem {}{} : {} := {}", 
                      name, 
                      pretty_lvls(lvl), 
                      typ.pretty(env, ind),
                      expr.pretty(env, ind)))
      }
      // Opaque: unsafe? opaque rec? <name> {lvl*}? : <typ> := <expr>
      Const::Opaque { name, lvl, typ, expr, safe } => {
        let typ = env.expr_cache.get(&typ)?; 
        let expr = env.expr_cache.get(&expr)?; 

        let rec_str = if matches!(expr, Expr::Fix(..)) { " rec" } else { "" };
        let safety_str = if *safe { "" } else { "unsafe " };
        Some(format!("{}opaque{} {}{} : {} := {}",
                      safety_str, 
                      rec_str, 
                      name, 
                      pretty_lvls(lvl), 
                      typ.pretty(env, ind),
                      expr.pretty(env, ind)))
      }
      Const::Definition { name, lvl, typ, expr, safe } => {
        let typ = env.expr_cache.get(&typ)?; 
        let expr = env.expr_cache.get(&expr)?; 

        let rec_str = if matches!(expr, Expr::Fix(..)) { " rec" } else { "" };
        let safety_str = match safe {
          DefSafety::Unsafe => "unsafe ",
          DefSafety::Safe => "",
          DefSafety::Partial => "partial "
        };

        Some(format!("{}def{} {}{} : {} := {}",
                      safety_str, 
                      rec_str,
                      name, 
                      pretty_lvls(lvl), 
                      typ.pretty(env, ind),
                      expr.pretty(env, ind)))
      }
      // Inductive Type:
      // ```lean
      // unsafe? inductive rec? <name> {lvl*}? (<params>{num_params}) : <typ> where
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
        let (bds, sort) = get_binders(typ, Some(params + indices));
        let bds: Vec<String> = bds.iter().map(|((n, bi), e)| with_binders(format!("{n} : {}", e.pretty(env, ind)), bi)).collect();
        let ctors_str = print_constructors(ind, env, ctors)?;
        let sort_sep = if *indices > 0 { " -> " } else { "" };
        let unsafe_str = if *safe { "" } else { "unsafe " };
        let rec_str = if *recr { " rec" } else { "" };
        let params_str = if *params > 0 { format!(" {}", bds[0..*params].join(" ")) } else { "".to_string() };
        Some(format!("{}inductive{} {}{}{} : {}{}{} where\n{}",
                      unsafe_str,
                      rec_str,
                      name,
                      pretty_lvls(lvl),
                      params_str, // print params
                      bds[*params..].join(" "), // print indices
                      sort_sep,
                      sort.pretty(env, ind),
                      ctors_str)) // print ctors
      }
      Const::Constructor { name, lvl, ind, typ, param, field, safe } => {
        // TODO
        let typ = env.expr_cache.get(&typ)?;  
        let ind = env.const_cache.get(&ind)?;  
        Some(format!("{}", name))
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
        let ind = env.const_cache.get(&ind)?;  
        let (.., ind_params, ind_indices) = 
        (match ind {
          Const::Inductive { name, lvl, typ, params, indices, .. } => {
            Some((name, typ, params, indices))
          },
          _ => None,
        })?;
        if *ind_params != *params || *ind_indices != *indices {
          return None
        }
        Some("".to_string())
      }
      Const::Quotient { .. } => {
        // TODO
        Some("".to_string())
      }
    }
  }

  pub fn get_internal_refs(&self, env: &Env) -> Vec<ConstCid> {
    match self {
      Const::Axiom { name, lvl, typ, safe } => {
        let typ = env.expr_cache.get(&typ).unwrap();
        typ.get_internal_refs()
      },
      Const::Theorem { name, lvl, typ, expr } => {
        let typ = env.expr_cache.get(&typ).unwrap();
        let expr = env.expr_cache.get(&expr).unwrap();
        let mut refs = typ.get_internal_refs();
        refs.extend(expr.get_internal_refs());
        refs
      },
      Const::Opaque { name, lvl, typ, expr, safe } => {
        let typ = env.expr_cache.get(&typ).unwrap();
        let expr = env.expr_cache.get(&expr).unwrap();
        let mut refs = typ.get_internal_refs();
        refs.extend(expr.get_internal_refs());
        refs
      },
      Const::Definition { name, lvl, typ, expr, safe } => {
        let typ = env.expr_cache.get(&typ).unwrap();
        let expr = env.expr_cache.get(&expr).unwrap();
        let mut refs = typ.get_internal_refs();
        refs.extend(expr.get_internal_refs());
        refs
      },
      Const::Inductive { name, lvl, typ, params, indices, ctors, recr, safe, refl, nest } => {
        let typ = env.expr_cache.get(&typ).unwrap();
        let mut refs = typ.get_internal_refs();
        for (_, ctorcid) in ctors {
          let ctor = env.expr_cache.get(&ctorcid).unwrap();
          refs.extend(ctor.get_internal_refs());
        }
        refs
      },
      Const::Constructor { name, lvl, ind, typ, param, field, safe } => {
        let typ = env.expr_cache.get(&typ).unwrap();
        typ.get_internal_refs()
      },
      Const::Recursor { lvl, ind, typ, params, indices, motives, minors, rules, k, safe } => {
        let typ = env.expr_cache.get(&typ).unwrap();
        typ.get_internal_refs()
      },
      Const::Quotient { kind } => {
        Vec::<ConstCid>::new()
      },
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
    params: usize,
    indices: usize,
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

#[cfg(test)]
pub mod tests {
  use crate::test::frequency;
  use crate::parse::utils::{
      BindCtx,
      GlobalCtx,
      UnivCtx,
  };

  use crate::expression::tests::{ExprEnv, arbitrary_exprenv, dummy_global_ctx};

  use crate::name::tests::arbitrary_ascii_name;

  use crate::universe::tests::dummy_univ_ctx;

  use im::Vector;

  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::*;

  #[derive(Clone, Debug, PartialEq)]
  pub struct ConstEnv {
    pub cnst: Const,
    pub env: Env
  }

  impl Arbitrary for DefSafety {
    fn arbitrary(g: &mut Gen) -> Self {
      let gen: usize = Arbitrary::arbitrary(g);
      let gen = gen % 3;
      match gen {
        0 => Self::Unsafe,
        1 => Self::Safe,
        2 => Self::Partial,
        _ => panic!()
      }
    }
  }

  fn arbitrary_pi(g: &mut Gen, depth: usize, bind_ctx: &BindCtx, univ_ctx: &UnivCtx, global_ctx: &GlobalCtx) -> ExprEnv {
    if depth > 0 {
      let name = arbitrary_ascii_name(g, 5);
      let typ: ExprEnv = arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), bind_ctx, univ_ctx, global_ctx);
      let mut bind_ctx = bind_ctx.clone();
      bind_ctx.push_front(name.clone());
      let trm: ExprEnv = arbitrary_pi(&mut Gen::new(g.size().saturating_sub(1)), depth.saturating_sub(1), &bind_ctx, univ_ctx, global_ctx);
      let mut env = typ.env;
      env.extend(trm.env);

      ExprEnv {
        expr:
          Expr::Pi(
            name,
            Arbitrary::arbitrary(g),
            Box::new(typ.expr),
            Box::new(trm.expr)
          ),
        env
      }
    }
    else {
      arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), &bind_ctx, univ_ctx, global_ctx)
    }
  }

  pub fn arbitrary_constenv(g: &mut Gen, name: Option<Name>, global_ctx: &GlobalCtx) -> ConstEnv {
    let name = if let Some(n) = name { n.clone() } else { arbitrary_ascii_name(g, 5) };
    let name = &name;

    let num_univs = usize::arbitrary(g) % 4;
    let univs: Vec<Name> = dummy_univ_ctx().iter().map(|n| n.clone()).collect();
    let univs = (&univs[..num_univs]).to_vec();
    let univs = &univs;
    let univ_ctx = Vector::from(univs.clone());

    let input: Vec<(usize, Box<dyn Fn(&mut Gen) -> ConstEnv>)> = vec![
      (100, Box::new(|g| {
        let expr_size = 60;

        let num_params = usize::arbitrary(g) % 5;
        let num_inds = usize::arbitrary(g) % 5;
        let num_ctors = usize::arbitrary(g) % 5;

        let typ = arbitrary_pi(&mut Gen::new(expr_size), num_params + num_inds, &Vector::new(), &univ_ctx, &global_ctx);

        let mut env = typ.env;

        let mut ctor_bind_ctx = Vector::new();
        ctor_bind_ctx.push_front(name.clone());
        for ((n, _), _) in get_binders(&typ.expr, None).0[..num_params].iter() {
          ctor_bind_ctx.push_front(n.clone());
        }

        let mut ctors = Vec::new();
        for _ in 0..num_ctors {
          let ctor_name = arbitrary_ascii_name(g, 5);
          let ctor_depth = usize::arbitrary(g) % 5;
          let ctor_type = arbitrary_pi(&mut Gen::new(expr_size), ctor_depth, &ctor_bind_ctx, &univ_ctx, &global_ctx);
          env.extend(ctor_type.env);
          ctors.push((ctor_name, ctor_type.expr));
        }

        let typcid = typ.expr.clone().store(&mut env).unwrap();
        let ctorcids = ctors.iter().fold(Vec::new(),
          |mut cids, (name, expr)| {
            let cid = expr.clone().store(&mut env).unwrap();
            cids.push((name.clone(), cid));
            cids
          });

        ConstEnv {
          cnst: Const::Inductive {
            name: name.clone(),
            lvl: univs.clone(),
            params: num_params,
            indices: num_inds,
            typ: typcid,
            ctors: ctorcids,
            recr: bool::arbitrary(g),
            safe: bool::arbitrary(g),
            refl: false,
            nest: false,
          },
          env: env
        }
      })),
      (100, Box::new(|g| {
        let rec = bool::arbitrary(g);

        let typ_size = usize::arbitrary(g) % 5;
        let typ = arbitrary_pi(g, typ_size, &Vector::new(), &univ_ctx, &global_ctx);

        let mut env = typ.env;

        let mut expr_bind_ctx = Vector::new();
        if rec {
          expr_bind_ctx.push_front(name.clone());
        }

        let exprenv = arbitrary_exprenv(g, &expr_bind_ctx, &univ_ctx, &global_ctx);
        env.extend(exprenv.env);
        let expr = if rec { Expr::Fix(name.clone(), Box::new(exprenv.expr)) } else {exprenv.expr};


        ConstEnv {
          cnst: Const::Definition {
            name: name.clone(),
            lvl: univs.clone(),
            typ: typ.expr.store(&mut env).unwrap(),
            expr: expr.store(&mut env).unwrap(),
            safe: DefSafety::arbitrary(g),
          },
          env: env
        }
      })),
      (100, Box::new(|g| {
        let rec = bool::arbitrary(g);

        let typ_size = usize::arbitrary(g) % 5;
        let typ = arbitrary_pi(g, typ_size, &Vector::new(), &univ_ctx, &global_ctx);

        let mut env = typ.env;

        let mut expr_bind_ctx = Vector::new();
        if rec {
          expr_bind_ctx.push_front(name.clone());
        }

        let exprenv = arbitrary_exprenv(g, &expr_bind_ctx, &univ_ctx, &global_ctx);
        env.extend(exprenv.env);
        let expr = if rec { Expr::Fix(name.clone(), Box::new(exprenv.expr)) } else {exprenv.expr};


        ConstEnv {
          cnst: Const::Opaque {
            name: name.clone(),
            lvl: univs.clone(),
            typ: typ.expr.store(&mut env).unwrap(),
            expr: expr.store(&mut env).unwrap(),
            safe: bool::arbitrary(g),
          },
          env: env
        }
      })),
      (100, Box::new(|g| {
        let typ_size = usize::arbitrary(g) % 5;
        let typ = arbitrary_pi(g, typ_size, &Vector::new(), &univ_ctx, &global_ctx);

        let mut env = typ.env;

        let exprenv = arbitrary_exprenv(g, &Vector::new(), &univ_ctx, &global_ctx);
        env.extend(exprenv.env);

        ConstEnv {
          cnst: Const::Theorem {
            name: name.clone(),
            lvl: univs.clone(),
            typ: typ.expr.store(&mut env).unwrap(),
            expr: exprenv.expr.store(&mut env).unwrap(),
          },
          env: env
        }
      })),
      (100, Box::new(|g| {
        let typ_size = usize::arbitrary(g) % 5;
        let typ = arbitrary_pi(g, typ_size, &Vector::new(), &univ_ctx, &global_ctx);

        let mut env = typ.env;

        ConstEnv {
          cnst: Const::Axiom {
            name: name.clone(),
            safe: bool::arbitrary(g),
            lvl: univs.clone(),
            typ: typ.expr.store(&mut env).unwrap(),
          },
          env: env
        }
      })),
    ];
    frequency(g, input)
  }

  impl Arbitrary for ConstEnv {
    fn arbitrary(g: &mut Gen) -> ConstEnv {
      arbitrary_constenv(g, None, &dummy_global_ctx())
    }
  }
}
