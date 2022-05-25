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
      let idx: usize = TryFrom::try_from(idx).unwrap();
      Rc::new(Expr::Var(idx))
    }
    _ => todo!()
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
    _ => todo!()
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
    _ => todo!()
  };
  conv_env.univs.insert(*univ_cid, univ.clone());
  univ
}
