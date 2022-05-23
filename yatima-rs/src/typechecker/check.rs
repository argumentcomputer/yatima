use crate::{
  typechecker::expression::*,
  typechecker::value::*,
  typechecker::evaluation::*,
  typechecker::equality::*,
};
use im::Vector;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckError {
  GenericError(String)
}

#[inline]
pub fn check_err<A>(msg: String) -> Result<A, CheckError> {
  Err(CheckError::GenericError(msg))
}

pub fn check(
  mut ctx: Vector<ThunkPtr>,
  term: &Rc<Expr>,
  mut env: Env,
  typ: Value
) -> Result<(), CheckError> {
  match &**term {
    Expr::Lam(lam_info, _, lam_bod) => {
      match typ {
        Value::Pi(pi_info, dom, cod, pi_env) => {
          if *lam_info != pi_info {
            return check_err(format!("Function type mismatch"))
          }
          // TODO: should we check that `lam_dom == dom`? It seems unecessarily wasteful
          let new_var = result(new_var(ctx.len()));
          ctx.push_back(dom);
          env.exprs.push_back(new_var.clone());
          let typ = eval(cod.clone(), extend_with_thunk(pi_env, new_var));
          check(ctx, lam_bod, env, typ)
        },

        _ => check_err(format!("Expected a function type")),
      }
    },
    Expr::Let(expr_typ, expr, body) => {
      let sort = infer(ctx.clone(), expr_typ, env.clone())?;
      match sort {
        Value::Sort(..) => (),
        _ => return check_err(format!("Expected a type to bind variable inside let")),
      }
      let expr_typ = eval(expr_typ.clone(), env.clone());
      check(ctx.clone(), expr, env.clone(), expr_typ.clone())?;
      ctx.push_back(result(expr_typ));
      env.exprs.push_back(suspend(expr.clone(), env.clone()));
      check(ctx, body, env, typ)
    },
    Expr::Fix(body) => {
      ctx.push_back(result(typ.clone()));
      env.exprs.push_back(suspend(term.clone(), env.clone()));
      check(ctx, body, env, typ)
    },
    _ => {
      let dep = ctx.len();
      let expected_typ = infer(ctx, term, env)?;
      if !equal(&typ, &expected_typ, dep) {
        return check_err(format!("Type mismatch"));
      }
      Ok(())
    },
  }
}

pub fn infer(
  _ctx: Vector<ThunkPtr>,
  _term: &Rc<Expr>,
  _env: Env,
) -> Result<Value, CheckError> {
  todo!()
}
