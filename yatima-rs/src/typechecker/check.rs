use crate::expression::{
    Literal,
    LitType,
  };
use crate::typechecker::{
  equality::*,
  evaluation::*,
  expression::*,
  universe::*,
  value::*,
};
use im::Vector;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckError {
  NotPi,
  NotSameBinder,
  NotTyp,
  ValueMismatch,
  CannotInferFix,
  CannotInferLam,
}

pub fn check(
  mut ctx: Vector<ThunkPtr>,
  term: &Rc<Expr>,
  mut env: Env,
  typ: Value,
) -> Result<(), CheckError> {
  match &**term {
    Expr::Lam(lam_info, _, lam_bod) => {
      match typ {
        Value::Pi(pi_info, dom, cod, pi_env) => {
          if *lam_info != pi_info {
            return Err(CheckError::NotSameBinder);
          }
          // TODO: should we check that `lam_dom == dom`? It seems unecessarily
          // wasteful
          let new_var = result(new_var(ctx.len()));
          ctx.push_back(dom);
          env.exprs.push_back(new_var.clone());
          let typ = eval(cod.clone(), extend_with_thunk(pi_env, new_var));
          check(ctx, lam_bod, env, typ)
        }

        _ => Err(CheckError::NotPi),
      }
    }
    Expr::Let(expr_typ, expr, body) => {
      let sort = infer(ctx.clone(), expr_typ, env.clone())?;
      match sort {
        Value::Sort(..) => (),
        _ => return Err(CheckError::NotTyp),
      }
      let expr_typ = eval(expr_typ.clone(), env.clone());
      check(ctx.clone(), expr, env.clone(), expr_typ.clone())?;
      ctx.push_back(result(expr_typ));
      env.exprs.push_back(suspend(expr.clone(), env.clone()));
      check(ctx, body, env, typ)
    }
    Expr::Fix(body) => {
      ctx.push_back(result(typ.clone()));
      env.exprs.push_back(suspend(term.clone(), env.clone()));
      check(ctx, body, env, typ)
    }
    _ => {
      let dep = ctx.len();
      let expected_typ = infer(ctx, term, env)?;
      if !equal(&typ, &expected_typ, dep) {
        return Err(CheckError::ValueMismatch);
      }
      Ok(())
    }
  }
}

pub fn infer(
  ctx: Vector<ThunkPtr>,
  term: &Rc<Expr>,
  env: Env,
) -> Result<Value, CheckError> {
  match &**term {
    Expr::Var(idx) => {
      let dep = ctx.len() - 1 - idx;
      Ok(force(&ctx[dep]))
    }
    Expr::App(fun, arg) => {
      let fun_typ = infer(ctx.clone(), fun, env.clone())?;
      match fun_typ {
        Value::Pi(_, dom, cod, mut pi_env) => {
          check(ctx.clone(), arg, env.clone(), force(&dom))?;
          let arg = suspend(arg.clone(), env);
          pi_env.exprs.push_back(arg);
          let typ = eval(cod, pi_env);
          Ok(typ)
        }
        _ => Err(CheckError::NotPi),
      }
    }
    Expr::Pi(..) => todo!(),
    Expr::Lam(..) => Err(CheckError::CannotInferLam),
    Expr::Let(..) => todo!(),
    Expr::Const(..) => todo!(),
    Expr::Sort(lvl) => {
      let lvl = reduce(&Rc::new(Univ::Succ(lvl.clone())));
      Ok(Value::Sort(lvl))
    }
    Expr::Lit(Literal::Nat(..)) => Ok(Value::Lty(LitType::Nat)),
    Expr::Lit(Literal::Str(..)) => Ok(Value::Lty(LitType::Str)),
    Expr::Lty(..) => {
      let one = Rc::new(Univ::Succ(Rc::new(Univ::Zero)));
      Ok(Value::Sort(one))
    }
    Expr::Fix(..) => Err(CheckError::CannotInferFix),
    _ => todo!() // Projections
  }
}
