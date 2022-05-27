use crate::{
  constant::ConstAnon,
  environment::{Env, ExprAnonCid, ConstAnonCid, UnivAnonCid},
  expression::ExprAnon,
  typechecker::universe::Univ,
  typechecker::expression::{Expr, Const},
  universe::UnivAnon,
};
use std::rc::Rc;
use alloc::collections::BTreeMap;

pub struct ConversionEnv {
  pub univs: BTreeMap<UnivAnonCid, Rc<Univ>>,
  pub exprs: BTreeMap<ExprAnonCid, Rc<Expr>>,
  pub consts: BTreeMap<ConstAnonCid, Rc<Const>>,
}

pub fn expr_from_anon(expr_cid: &ExprAnonCid, cid_env: &Env, conv_env: &mut ConversionEnv) -> Rc<Expr> {
  match conv_env.exprs.get(expr_cid) {
    Some(expr) => return expr.clone(),
    None => (),
  }
  let expr = match cid_env.expr_anon.get(expr_cid).unwrap() {
    ExprAnon::Var(idx) => {
      let idx = TryFrom::try_from(idx).unwrap();
      Rc::new(Expr::Var(idx))
    }
    ExprAnon::Sort(univ_cid) => {
      let lvl = univ_from_anon(univ_cid, cid_env, conv_env);
      Rc::new(Expr::Sort(lvl))
    },
    ExprAnon::Const(const_cid, univ_cids) => {
      let cnst = const_from_anon(const_cid, cid_env, conv_env);
      let lvls = univ_cids
        .iter()
        .map(|univ_cid| univ_from_anon(univ_cid, cid_env, conv_env))
        .collect();
      Rc::new(Expr::Const(cnst, lvls))
    },
    ExprAnon::App(fun_cid, arg_cid) => {
      let fun = expr_from_anon(fun_cid, cid_env, conv_env);
      let arg = expr_from_anon(arg_cid, cid_env, conv_env);
      Rc::new(Expr::App(fun, arg))
    },
    ExprAnon::Lam(binfo, dom_cid, bod_cid) => {
      let dom = expr_from_anon(dom_cid, cid_env, conv_env);
      let bod = expr_from_anon(bod_cid, cid_env, conv_env);
      Rc::new(Expr::Lam(*binfo, dom, bod))
    },
    ExprAnon::Pi(binfo, dom_cid, cod_cid) => {
      let dom = expr_from_anon(dom_cid, cid_env, conv_env);
      let cod = expr_from_anon(cod_cid, cid_env, conv_env);
      Rc::new(Expr::Pi(*binfo, dom, cod))
    },
    ExprAnon::Let(typ_cid, exp_cid, bod_cid) => {
      let typ = expr_from_anon(typ_cid, cid_env, conv_env);
      let exp = expr_from_anon(exp_cid, cid_env, conv_env);
      let bod = expr_from_anon(bod_cid, cid_env, conv_env);
      Rc::new(Expr::Let(typ, exp, bod))
    },
    ExprAnon::Lit(lit) => Rc::new(Expr::Lit(lit.clone())),
    ExprAnon::Lty(lty) => Rc::new(Expr::Lty(*lty)),
    ExprAnon::Fix(bod_cid) => {
      let bod = expr_from_anon(bod_cid, cid_env, conv_env);
      Rc::new(Expr::Fix(bod))
    },
  };
  conv_env.exprs.insert(*expr_cid, expr.clone());
  expr
}

pub fn const_from_anon(const_cid: &ConstAnonCid, cid_env: &Env, conv_env: &mut ConversionEnv) -> Rc<Const> {
  match conv_env.consts.get(const_cid) {
    Some(cnst) => return cnst.clone(),
    None => (),
  }
  let cnst = match cid_env.const_anon.get(const_cid).unwrap() {
    ConstAnon::Quotient(kind) => Rc::new(Const::Quotient{ kind: *kind }),
    ConstAnon::Axiom(..) => todo!(),
    ConstAnon::Theorem(..) => todo!(),
    ConstAnon::Opaque(..) => todo!(),
    ConstAnon::Definition(..) => todo!(),
    ConstAnon::Inductive(..) => todo!(),
    ConstAnon::Constructor(..) => todo!(),
    ConstAnon::Recursor(..) => todo!(),
  };
  conv_env.consts.insert(*const_cid, cnst.clone());
  cnst
}

pub fn univ_from_anon(univ_cid: &UnivAnonCid, cid_env: &Env, conv_env: &mut ConversionEnv) -> Rc<Univ> {
  match conv_env.univs.get(univ_cid) {
    Some(expr) => return expr.clone(),
    None => (),
  }
  let univ = match cid_env.univ_anon.get(univ_cid).unwrap() {
    UnivAnon::Zero => Rc::new(Univ::Zero),
    UnivAnon::Succ(lvl_cid) => {
      let lvl = univ_from_anon(lvl_cid, cid_env, conv_env);
      Rc::new(Univ::Succ(lvl))
    },
    UnivAnon::Max(l_lvl_cid, r_lvl_cid) => {
      let l_lvl = univ_from_anon(l_lvl_cid, cid_env, conv_env);
      let r_lvl = univ_from_anon(r_lvl_cid, cid_env, conv_env);
      Rc::new(Univ::Max(l_lvl, r_lvl))
    },
    UnivAnon::IMax(l_lvl_cid, r_lvl_cid) => {
      let l_lvl = univ_from_anon(l_lvl_cid, cid_env, conv_env);
      let r_lvl = univ_from_anon(r_lvl_cid, cid_env, conv_env);
      Rc::new(Univ::IMax(l_lvl, r_lvl))
    },
    UnivAnon::Param(idx) => {
      let idx = TryFrom::try_from(idx).unwrap();
      Rc::new(Univ::Var(idx))
    },
  };
  conv_env.univs.insert(*univ_cid, univ.clone());
  univ
}
