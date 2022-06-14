use crate::constant::DefSafety;
use crate::typechecker::{
  expression::*,
  universe::*,
  value::*,
};
use im::Vector;
use std::{
  cell::RefCell,
  rc::Rc,
};

#[inline]
pub fn result(val: Value) -> ThunkPtr { Rc::new(RefCell::new(Thunk::Res(val))) }

#[inline]
pub fn suspend(expr: ExprPtr, env: Env) -> ThunkPtr {
  Rc::new(RefCell::new(Thunk::Sus(expr, env)))
}

#[inline]
pub fn force(thunk: &ThunkPtr) -> Value {
  let borrow = thunk.borrow();
  match &*borrow {
    Thunk::Res(val) => val.clone(),
    Thunk::Sus(expr, env) => {
      let val = eval(expr.clone(), env.clone());
      drop(borrow);
      let mut mut_borrow = thunk.borrow_mut();
      *mut_borrow = Thunk::Res(val.clone());
      val
    }
  }
}

pub fn eval(expr: ExprPtr, mut env: Env) -> Value {
  match &*expr {
    Expr::Var(idx) => force(&env.exprs[*idx]),
    Expr::Sort(lvl) => {
      // Value::Sort only takes fully reduced levels, so we instantiate all
      // variables using the universe environment and reduce
      let lvl = inst_bulk_reduce(lvl, &env.univs);
      Value::Sort(lvl)
    }
    Expr::Const(cnst, cnst_univs) => {
      let univs = cnst_univs
        .iter()
        .map(|lvl| inst_bulk_reduce(lvl, &env.univs))
        .collect();
      eval_const(cnst, univs)
    }
    Expr::App(fun, arg) => {
      let arg = suspend(arg.clone(), env.clone());
      let fun = eval(fun.clone(), env.clone());
      match fun {
        Value::Lam(_, body, lam_env) => {
          let mut lam_env = lam_env.clone();
          lam_env.exprs.push_front(arg);
          eval(body.clone(), lam_env)
        }
        Value::App(var @ Neutral::FVar(..), args) => {
          let mut args = args.clone();
          args.push_front(arg);
          Value::App(var, args)
        }
        Value::App(Neutral::Const(cnst, cnst_univs), args) => {
          let univs = cnst_univs
            .iter()
            .map(|lvl| inst_bulk_reduce(lvl, &env.univs))
            .collect();
          apply_const(cnst, univs, arg, args)
        }
        _ => unreachable!(),
      }
    }
    Expr::Lam(binfo, _, body) => Value::Lam(*binfo, body.clone(), env),
    Expr::Pi(binfo, dom, cod) => {
      let dom = suspend(dom.clone(), env.clone());
      Value::Pi(*binfo, dom, cod.clone(), env)
    }
    Expr::Let(_, expr, body) => {
      env.exprs.push_front(suspend(expr.clone(), env.clone()));
      eval(body.clone(), env)
    }
    Expr::Lit(lit) => Value::Lit(lit.clone()),
    Expr::Lty(lty) => Value::Lty(*lty),
    Expr::Fix(body) => {
      let body = body.clone();
      let itself = suspend(expr, env.clone());
      env.exprs.push_front(itself);
      eval(body, env)
    },
    _ => todo!() // Projections
  }
}

#[inline]
pub fn eval_const(cnst: &ConstPtr, univs: Vector<UnivPtr>) -> Value {
  match &**cnst {
    Const::Theorem { expr, .. }
    | Const::Definition { safe: DefSafety::Safe, expr, .. } => {
      eval(expr.clone(), Env { exprs: Vector::new(), univs })
    }
    Const::Definition { safe: DefSafety::Unsafe, .. } => {
      panic!("Cannot use unsafe definitions inside types")
    }
    _ => Value::App(Neutral::Const(cnst.clone(), univs), Vector::new()),
  }
}

#[inline]
pub fn apply_const(
  cnst: ConstPtr,
  univs: Vector<UnivPtr>,
  arg: ThunkPtr,
  mut args: Vector<ThunkPtr>,
) -> Value {
  // Assumes a partial application of k to args, which means in particular, that
  // it is in normal form
  match &*cnst {
    Const::Recursor { params, motives, minors, indices, rules, .. } => {
      let major_idx = params + motives + minors + indices;
      if args.len() != major_idx {
        args.push_front(arg);
        return Value::App(Neutral::Const(cnst, univs), args);
      }
      match force(&arg) {
        Value::App(Neutral::Const(ctor, _), ctor_args) => {
          match &*ctor {
            Const::Constructor { .. } => {
              // Since we assume expressions are previously type checked, we
              // know that this constructor must have an
              // associated recursion rule
              let rule = rules.get(&Rc::as_ptr(&ctor)).unwrap();
              // Indices are not needed used at all in recursion rules
              args.slice(indices..);
              // The number of parameters in the constructor is not necessarily
              // equal to the number of parameters in the recursor in nested
              // inductive types, but the rule knows how many arguments to take
              let mut exprs = ctor_args.take(rule.nfields);
              exprs.append(args);
              return eval(rule.rhs.clone(), Env { exprs, univs });
            }
            _ => (),
          }
        }
        _ => (),
      }
    }
    Const::Quotient { .. } => {
      todo!()
    }
    _ => (),
  }
  args.push_front(arg);
  Value::App(Neutral::Const(cnst, univs), args)
}
