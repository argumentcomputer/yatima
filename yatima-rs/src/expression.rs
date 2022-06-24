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
    UnivCid,
    UnivMetaCid,
  },
  name::Name,
  nat::Nat, typechecker::check::infer, universe::Univ,
};
use serde::{
  Deserialize,
  Serialize,
};

use im::{
  Vector,
};

use alloc::{
  fmt,
  boxed::Box,
  string::String,
};
use libipld::serde::to_ipld;

use multihash::{
  Code,
  MultihashDigest,
};

use num_traits::{
  One,
  Zero,
};

use libipld::{
  cbor::DagCborCodec,
  codec::Codec,
};

use crate::parse::utils::with_binders;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Literal {
  Nat(Nat),
  Str(String),
}

impl fmt::Display for Literal {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Literal::Nat(n) => write!(f, "{}", n),
      Literal::Str(str) => write!(f, "\"{}\"", str)
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LitType {
  Nat,
  Str,
}

impl fmt::Display for LitType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      LitType::Nat => write!(f, "#Nat"),
      LitType::Str => write!(f, "#Str")
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinderInfo {
  Default,
  Implicit,
  StrictImplicit,
  InstImplicit,
}

/// Yatima Expressions
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Expr {
  /// Variables
  Var(Name, Nat),
  /// Type Universes
  Sort(UnivCid),
  /// Global references to a Constant, with universe arguments
  Const(Name, ConstCid, Vec<UnivCid>),
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
  /// Projections 
  Proj(Nat, Box<Expr>),
}

impl Expr {
  pub fn cid(&self, env: &mut Env) -> Result<ExprCid, EnvError> {
    match self {
      Expr::Var(name, idx) => {
        let anon = ExprAnon::Var(idx.clone()).store(env)?;
        let meta = ExprMeta::Var(name.clone()).store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::Sort(univ_cid) => {
        let anon = ExprAnon::Sort(univ_cid.anon).store(env)?;
        let meta = ExprMeta::Sort(univ_cid.meta).store(env)?;
        Ok(ExprCid { anon, meta })
      }
      Expr::Const(name, const_cid, univ_cids) => {
        let mut univ_anons = Vec::new();
        let mut univ_metas = Vec::new();
        for cid in univ_cids {
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
      Expr::Proj(idx, exp) => {
        let exp_cid = exp.cid(env)?;
        let anon = ExprAnon::Proj(idx.clone(), exp_cid.anon).store(env)?;
        let meta = ExprMeta::Proj(idx.clone(), exp_cid.meta).store(env)?;
        Ok(ExprCid { anon, meta })
      }
    }
  }

  pub fn store(self, env: &mut Env) -> Result<ExprCid, EnvError> {
    let cid = self.cid(env)?;
    env.insert_expr_cache(cid, self);
    Ok(cid)
  }

  pub fn shift(self, inc: &Nat, dep: &Option<Nat>) -> Self {
    if *inc == Nat::zero() {
      return self.clone();
    }
    match self {
      Self::Var(nam, idx) => match dep {
        // only increment free variables
        Some(dep) if idx < *dep => Self::Var(nam, idx),
        _ => Self::Var(nam, idx + inc),
      },
      Self::Lam(nam, bind, typ, bod) => {
        Self::Lam(
          nam,
          bind,
          Box::new((*typ).shift(inc, dep)),
          // must increment depth because we are within the scope of the new
          // binder `nam`
          Box::new((*bod).shift(inc, &dep.as_ref().map(|x| x + Nat::one()))),
        )
      }
      Self::App(fun, arg) => {
        Self::App(Box::new(fun.shift(inc, dep)), Box::new(arg.shift(inc, dep)))
      }
      Self::Pi(nam, bind, dom, rng) => Self::Pi(
        nam,
        bind,
        Box::new(dom.shift(inc, dep)),
        Box::new(rng.shift(inc, &dep.as_ref().map(|x| x + Nat::one()))),
      ),
      Self::Let(nam, typ, exp, bod) => Self::Let(
        nam,
        Box::new(typ.shift(inc, dep)),
        Box::new(exp.shift(inc, dep)),
        Box::new(bod.shift(inc, &dep.as_ref().map(|x| x + Nat::one()))),
      ),
      Self::Fix(nam, x) => Self::Fix(
        nam,
        Box::new(x.shift(inc, &dep.as_ref().map(|x| x + Nat::one()))),
      ),
      x => x,
    }
  }

  pub fn pretty(&self, env: &Env, ind: bool) -> String {
    
    fn is_atom(expr: &Expr) -> bool {
      matches!(expr, Expr::Const(..) | Expr::Var(..) | Expr::Lit(..) | Expr::Lty(..))
    }

    // Basic logic around parantheses, makes sure we don't do atoms.
    fn parens(env: &Env, ind: bool, expr: &Expr) -> String {
      let mut is_prop = false;
      if let Expr::Sort(univcid) = expr {
        let univ = env.get_univ_cache(univcid).unwrap();
        is_prop = matches!(univ, Univ::Zero)
      }

      if is_atom(expr) || is_prop
      {
        expr.pretty(env, ind)
      }
      else {
        format!("({})", expr.pretty(env, ind))
      }
    }

    fn lambdas(env: &Env, ind: bool, name: &str, bi: &BinderInfo, typ: &Expr, body: &Expr) -> String {
      let bdd_var = with_binders(format!("{name} : {}", typ.pretty(env, ind)), bi);
      match body {
        Expr::Lam(name2, bi2, typ2, body2) => {
          format!("{} {}", bdd_var, lambdas(env, ind, name2, bi2, typ2, body2))
        }
        _ => format!("{} => {}", bdd_var, body.pretty(env, ind)),
      }
    }

    // Same thing as lamdba
    fn foralls(env: &Env, ind: bool, name: &str, bi: &BinderInfo, typ: &Expr, body: &Expr) -> String {
      let bdd_var = with_binders(format!("{name} : {}", typ.pretty(env, ind)), bi);
      match body {
        Expr::Pi(name2, bi2, typ2, body2) => {
          format!("{} {}", bdd_var, foralls(env, ind, name2, bi2, typ2, body2))
        }
        _ => format!("{} → {}", bdd_var, body.pretty(env, ind)),
      }
    }

    // Handle nested applications
    fn apps(env: &Env, ind: bool, fun: &Expr, arg: &Expr) -> String {
      match (fun, arg) {
        (Expr::App(fun, arg1), arg2) => {
          format!("{} {}", apps(env, ind, fun, arg1), parens(env, ind, arg2))
        }
        (fun, arg) => {
          format!("{} {}", parens(env, ind, fun), parens(env, ind, arg))
        }
      }
    }

    match self {
      Expr::Var(name, idx) => 
      if ind {
        format!("{}^{}", name, idx)
      }
      else {
        name.to_string()
      },
      Expr::Sort(cid) => {
        let univ = env.get_univ_cache(cid).unwrap();
        if *univ == Univ::Zero {
          return "Prop".to_string();
        }
        format!("Sort {}", univ.pretty(ind))
      },
      Expr::Const(name, _, univs) => {
        let univs: Vec<String> = univs.iter().map(
          |univ_cid| env.get_univ_cache(univ_cid).unwrap().pretty(ind)).collect();
        if univs.len() > 0 {
          format!("{}.{{{}}}", name, univs.join(" "))
        }
        else {
          format!("{}", name)
        }
      },
      Expr::App(fun, arg) => {
        format!("{}", apps(env, ind, fun, arg))
      },
      Expr::Lam(name, bi, typ, body) => {
        format!("λ {}", lambdas(env, ind, name, bi, typ, body))
      },
      Expr::Pi(name, bi, typ, body) => { // Very similar to lambdas
        format!("Π {}", foralls(env, ind, name, bi, typ, body))
      },
      Expr::Let(name, typ, expr, body) => {
        format!("let {} : {} := {} in {}", name, typ.pretty(env, ind), expr.pretty(env, ind), body.pretty(env, ind))
      },
      Expr::Lit(lit) => {
        format!("{}", lit)
      },
      Expr::Lty(lty) => {
        format!("{}", lty)
      },
      Expr::Fix(_, expr) => {
        format!("{}", expr.pretty(env, ind)) 
      },
      _ => todo!() // Projections
    }
  }

  pub fn get_internal_refs(&self) -> Vec<ConstCid> {
    match self {
      Expr::Const(name, cid, univs) => {
        Vec::from(vec![*cid])
      },
      Expr::App(fun, arg) => {
        let mut refs = fun.get_internal_refs();
        refs.extend(arg.get_internal_refs());
        refs
      },
      Expr::Lam(name, bi, typ, body) => {
        let mut refs = typ.get_internal_refs();
        refs.extend(body.get_internal_refs());
        refs
      },
      Expr::Pi(name, bi, typ, body) => { 
        let mut refs = typ.get_internal_refs();
        refs.extend(body.get_internal_refs());
        refs
      },
      Expr::Let(name, typ, expr, body) => {
        let mut refs = typ.get_internal_refs();
        refs.extend(expr.get_internal_refs());
        refs.extend(body.get_internal_refs());
        refs
      },
      Expr::Fix(_, expr) => {
        expr.get_internal_refs()
      },
      Expr::Proj(idx, expr) => {
        expr.get_internal_refs()
      }
      _ => Vec::<ConstCid>::new()
    }
  }
}

impl fmt::Display for Expr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.pretty(&Env::new(), false))
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
/// ExprMeta::Proj => [10, <expr>]
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
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
  Proj(Nat, ExprMetaCid),
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
    env.insert_expr_meta(cid, self);
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
/// ExprAnon::Proj => [10, <expr>]
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
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
  Proj(Nat, ExprAnonCid),
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
    env.insert_expr_anon(cid, self);
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

  use crate::universe::{Univ, tests::arbitrary_univ};

  use im::{
    OrdMap,
    Vector,
  };

  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use crate::name::tests::arbitrary_ascii_name;

  use super::*;

  pub fn dummy_const_cid(ind: u8) -> ConstCid {
    let anon: ConstAnonCid = ConstAnonCid::new(Code::Sha3_256.digest(&[ind]));
    let meta: ConstMetaCid = ConstMetaCid::new(Code::Sha3_256.digest(&[ind]));
    ConstCid { anon, meta }
  }

  pub fn dummy_global_ctx() -> GlobalCtx {
    OrdMap::from(vec![
      (Name::from("foo"), dummy_const_cid(0)),
      (Name::from("Nat"), dummy_const_cid(1)),
      (Name::from("Nat.zero"), dummy_const_cid(2)),
      (Name::from("Nat.succ"), dummy_const_cid(3))
    ])
  }

  pub fn dummy_univ_ctx() -> UnivCtx {
    Vector::from(vec![Name::from("w"), Name::from("v"), Name::from("u")])
  }

  #[derive(PartialEq, Clone, Debug)]
  pub struct ExprEnv {
    pub expr: Expr,
    pub env: Env,
  }

  // TODO can I #[derive(Arbitrary)]?
  impl Arbitrary for BinderInfo {
    fn arbitrary(g: &mut Gen) -> Self {
      let gen: usize = Arbitrary::arbitrary(g);
      let gen = gen % 4;
      match gen {
        0 => Self::Default,
        1 => Self::Implicit,
        2 => Self::StrictImplicit,
        3 => Self::InstImplicit,
        _ => panic!()
      }
    }
  }
  impl Arbitrary for Literal {
    fn arbitrary(g: &mut Gen) -> Self {
      let gen: usize = Arbitrary::arbitrary(g);
      let gen = gen % 2;
      match gen {
        0 => {
          let nat: usize = Arbitrary::arbitrary(g);
          Self::Nat(nat.into())
        }
        1 => {
          let len: usize = Arbitrary::arbitrary(g);
          let len = len % 10;
          let str: String = arbitrary_ascii_name(g, len).to_string();
          Self::Str(str)
        }
        _ => panic!()
      }
    }
  }
  impl Arbitrary for LitType {
    fn arbitrary(g: &mut Gen) -> Self {
      let gen: usize = Arbitrary::arbitrary(g);
      let gen = gen % 2;
      match gen {
        0 => Self::Nat,
        1 => Self::Str,
        _ => panic!()
      }
    }
  }

  fn arbitrary_sort(univ_ctx: &UnivCtx) -> ExprEnv {
    let mut env = Env::new();
    let univ: Univ = arbitrary_univ(&mut Gen::new(50), univ_ctx);
    let univ_cid = univ.store(&mut env).unwrap();
    ExprEnv {
      expr: Expr::Sort(univ_cid),
      env
    }
  }

  pub fn arbitrary_exprenv(g: &mut Gen, bind_ctx: &BindCtx, univ_ctx: &UnivCtx, global_ctx: &GlobalCtx) -> ExprEnv {
    let rec_freq = g.size().saturating_sub(10);
    let input: Vec<(usize, Box<dyn Fn(&mut Gen) -> ExprEnv>)> = vec![
      (100, Box::new(|g| {
        let gen = usize::arbitrary(g);
        if bind_ctx.len() > 0 {
          let gen = gen % bind_ctx.len();
          let n = &bind_ctx[gen];
          let (i, _) = bind_ctx.iter().enumerate().find(|(_, x)| *x == n).unwrap();
          ExprEnv {
            expr: Expr::Var(n.clone(), i.into()),
            env: Env::new()
          }
        }
        else {
          if global_ctx.len() > 0 {
            let gen = gen % global_ctx.len();
            // global context must be non-empty
            let (n, cid) = global_ctx.iter().nth(gen.try_into().unwrap()).unwrap();
            ExprEnv {
              expr: Expr::Const(n.to_owned(), cid.to_owned(), vec![]),
              env: Env::new()
            }
          }
          else { arbitrary_sort(univ_ctx) }
        }
      })),
      (rec_freq, Box::new(|g| {
        let fun: ExprEnv = arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), bind_ctx, univ_ctx, global_ctx);
        let arg: ExprEnv = arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), bind_ctx, univ_ctx, global_ctx);
        let mut env = fun.env;
        env.extend(arg.env);
        ExprEnv {
          expr:
            Expr::App(
              Box::new(fun.expr),
              Box::new(arg.expr)
            ),
          env: env
        }
      })),
      (rec_freq.saturating_sub(25), Box::new(|g| {
        let typ: ExprEnv = arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), bind_ctx, univ_ctx, global_ctx);
        let trm: ExprEnv = arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), bind_ctx, univ_ctx, global_ctx);
        let name = arbitrary_ascii_name(g, 5);
        let mut bind_ctx = bind_ctx.clone();
        bind_ctx.push_front(name.clone());
        let bod: ExprEnv = arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), &bind_ctx, univ_ctx, global_ctx);
        let mut env = typ.env;
        env.extend(trm.env);
        env.extend(bod.env);
        ExprEnv {
          expr:
            Expr::Let(
              name,
              Box::new(typ.expr),
              Box::new(trm.expr),
              Box::new(bod.expr)
            ),
          env: env
        }
      })),
      (rec_freq, Box::new(|g| {
        let name = arbitrary_ascii_name(g, 5);
        let typ: ExprEnv = arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), &bind_ctx, univ_ctx, global_ctx);
        let mut bind_ctx = bind_ctx.clone();
        bind_ctx.push_front(name.clone());
        let trm: ExprEnv = arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), &bind_ctx, univ_ctx, global_ctx);
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
          env: env
        }
      })),
      (rec_freq, Box::new(|g| {
        let name = arbitrary_ascii_name(g, 5);
        let typ: ExprEnv = arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), &bind_ctx, univ_ctx, global_ctx);
        let mut bind_ctx = bind_ctx.clone();
        bind_ctx.push_front(name.clone());
        let trm: ExprEnv = arbitrary_exprenv(&mut Gen::new(g.size().saturating_sub(1)), &bind_ctx, univ_ctx, global_ctx);
        let mut env = typ.env;
        env.extend(trm.env);
        ExprEnv {
          expr:
            Expr::Lam(
              name,
              Arbitrary::arbitrary(g),
              Box::new(typ.expr),
              Box::new(trm.expr)
            ),
          env: env
        }
      })),
      (100, Box::new(|_| {
        arbitrary_sort(univ_ctx)
      })),
      (100, Box::new(|g| {
        ExprEnv {
          expr: Expr::Lit(Arbitrary::arbitrary(g)),
          env: Env::new()
        }
      })),
      (100, Box::new(|g| {
        ExprEnv {
          expr: Expr::Lty(Arbitrary::arbitrary(g)),
          env: Env::new()
        }
      })),
      (100, Box::new(|g| {
        if global_ctx.len() > 0 {
          let mut env = Env::new();

          let num_univs: usize = Arbitrary::arbitrary(g);
          let num_univs = num_univs % 3;
          let mut univs = Vec::new();
          for _ in 0..num_univs {
            let univ: Univ = arbitrary_univ(&mut Gen::new(50), univ_ctx);
            univs.push(univ.store(&mut env).unwrap());
          }

          let const_idx: usize = Arbitrary::arbitrary(g);
          let const_idx = const_idx % global_ctx.len();

          let cnst = global_ctx.iter().nth(const_idx).unwrap();

          ExprEnv {
            expr: Expr::Const(cnst.0.to_owned(), cnst.1.to_owned(), univs),
            env: env
          }
        }
        else { arbitrary_sort(univ_ctx) }
      })),
    ];
    frequency(g, input)
  }

  impl Arbitrary for ExprEnv {
    fn arbitrary(g: &mut Gen) -> Self {
      arbitrary_exprenv(g, &Vector::new(), &dummy_univ_ctx(), &dummy_global_ctx())
    }
  }
}
