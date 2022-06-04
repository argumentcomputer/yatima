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
  nat::Nat,
};
use serde::{
  Deserialize,
  Serialize,
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Literal {
  Nat(Nat),
  Str(String),
}

impl fmt::Display for Literal {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Literal::Nat(n) => write!(f, "{}", n),
      Literal::Str(str) => write!(f, "{}", str)
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
    write!(f, "{}", self)
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

#[derive(PartialEq, Clone, Debug)]
pub struct ExprEnv {
  pub expr: Expr,
  pub env: Env,
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

  /// The input `Vector : ∀ (A: Type) -> ∀ (n: Nat) -> Sort 0` with depth 1 returns:
  ///   - string: `(A: Type)` 
  ///   - type: `∀ (n: Nat) -> Sort 0`
  /// This is useful for printing defs
  /// sort of the inverse of parse_bound_expressions?
  /// Note that this doesn't fail -- it just stops parsing if it hits a non-pi expr
  pub fn parse_binders(&self, env: &Env, ind: bool, depth: Nat) -> (String, &Expr) {
    // This feels slightly hacky
    fn with_binders(var: String, bi: &BinderInfo) -> String {
      match bi {
        BinderInfo::Default => format!("({})", var),
        BinderInfo::Implicit => format!("{{{}}}", var),
        BinderInfo::InstImplicit => format!("[{}]", var),
        BinderInfo::StrictImplicit => format!("{{{{{}}}}}", var),
      }
    }

    if depth == Nat::from(0 as u32) {
      ("".to_string(), self)
    } else {
      match self {
        Expr::Pi(name, bi, typ, expr) => {
          let bdd_var = with_binders(format!("{name} : {}", typ.pretty(env, ind)), bi);
          let (binders, remaining) = expr.parse_binders(env, ind, Nat::from(u32::MAX));
          (format!("{} {}", bdd_var, binders), remaining)
        },
        _ => ("".to_string(), self)
      }
    }
    
  }

  /// this is the inverse of parse_bound_expression?
  pub fn print_bound_expression(&self) -> String {
    "".to_string()
  }

  pub fn pretty(&self, env: &Env, ind: bool) -> String {
    
    fn is_atom(expr: &Expr) -> bool {
      matches!(expr, Expr::Var(..) | Expr::Sort(..) | Expr::Lit(..) | Expr::Lty(..))
    }

    // Basic logic around parantheses, makes sure we don't do atoms.
    fn parens(env: &Env, ind: bool, expr: &Expr) -> String {
      if is_atom(expr) {
        expr.pretty(env, ind)
      }
      else {
        format!("({})", expr.pretty(env, ind))
      }
    }

    // This feels slightly hacky
    fn with_binders(var: String, bi: &BinderInfo) -> String {
      match bi {
        BinderInfo::Default => format!("({})", var),
        BinderInfo::Implicit => format!("{{{}}}", var),
        BinderInfo::InstImplicit => format!("[{}]", var),
        BinderInfo::StrictImplicit => format!("{{{{{}}}}}", var),
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
        Expr::Lam(name2, bi2, typ2, body2) => {
          format!("{} {}", bdd_var, foralls(env, ind, name2, bi2, typ2, body2))
        }
        _ => format!("{} → {}", bdd_var, body.pretty(env, ind)),
      }
    }

    // Handle nested applications
    fn apps(env: &Env, ind: bool, fun: &Expr, arg: &Expr) -> String {
      match (fun, arg) {
        (Expr::App(fun, arg1), Expr::App(f, arg2)) => {
          // Not sure why we need this case, but this was in lang-alpha
          format!(
            "{} ({})",
            apps(env, ind, fun, arg1),
            apps(env, ind, f, arg2)
          )
        }
        (Expr::App(fun, arg1), arg2) => {
          format!("{} {}", apps(env, ind, fun, arg1), parens(env, ind, arg2))
        }
        (fun, Expr::App(fun2, arg)) => {
          format!("{} ({})", parens(env, ind, fun), apps(env, ind, fun2, arg))
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
        format!("Sort {}", env.get_univ_cache(cid).unwrap().pretty(ind))
      },
      Expr::Const(name, _, _) => format!("{}", name),
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
      EnvCtx,
      GlobalCtx,
      UnivCtx,
  };

  use crate::universe::Univ;

  use im::{
    OrdMap,
    Vector,
  };

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

  use super::*;
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use crate::name::tests::arbitrary_ascii_name;

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

  impl Arbitrary for ExprEnv {
    fn arbitrary(g: &mut Gen) -> Self {
      let rec_freq = g.size().saturating_sub(50);
      let input: Vec<(usize, Box<dyn Fn(&mut Gen) -> ExprEnv>)> = vec![
        (100, Box::new(|_| {
          ExprEnv {
            expr: Expr::Var(Name::from("_temp"), 0u8.into()),
            env: Env::new()
          }
        })),
        (rec_freq, Box::new(|g| {
          let fun: ExprEnv = Arbitrary::arbitrary(&mut Gen::new(g.size().saturating_sub(1)));
          let arg: ExprEnv = Arbitrary::arbitrary(&mut Gen::new(g.size().saturating_sub(1)));
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
        (rec_freq, Box::new(|g| {
          let typ: ExprEnv = Arbitrary::arbitrary(&mut Gen::new(g.size().saturating_sub(1)));
          let trm: ExprEnv = Arbitrary::arbitrary(&mut Gen::new(g.size().saturating_sub(1)));
          let mut env = typ.env;
          env.extend(trm.env);
          ExprEnv {
            expr:
              Expr::Pi(
                arbitrary_ascii_name(g, 5),
                Arbitrary::arbitrary(g),
                Box::new(typ.expr),
                Box::new(trm.expr)
              ),
            env: env
          }
        })),
        (rec_freq, Box::new(|g| {
          let typ: ExprEnv = Arbitrary::arbitrary(&mut Gen::new(g.size().saturating_sub(1)));
          let trm: ExprEnv = Arbitrary::arbitrary(&mut Gen::new(g.size().saturating_sub(1)));
          let mut env = typ.env;
          env.extend(trm.env);
          ExprEnv {
            expr:
              Expr::Lam(
                arbitrary_ascii_name(g, 5),
                Arbitrary::arbitrary(g),
                Box::new(typ.expr),
                Box::new(trm.expr)
              ),
            env: env
          }
        })),
        (100, Box::new(|g| {
          let mut env = Env::new();
          let univ: Univ = Arbitrary::arbitrary(g);
          let univ_cid = univ.store(&mut env).unwrap();
          ExprEnv {
            expr: Expr::Sort(univ_cid),
            env: env
          }
        })),
      ];
      frequency(g, input)
    }
  }
}
