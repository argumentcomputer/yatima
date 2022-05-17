use crate::{
  typechecker::universe::*,
  typechecker::expression::*,
  typechecker::value::*,
};
use im::Vector;
use std::rc::Rc;
use std::cell::RefCell;

pub fn suspend(u: Comp) -> ThunkPtr {
  Rc::new(RefCell::new(Thunk::Sus(u)))
}

pub fn force(thunk: ThunkPtr) -> Value {
  let borrow = thunk.borrow();
  match &*borrow {
    Thunk::Res(val) => {
      val.clone()
    },
    Thunk::Sus(u) => {
      let val = eval(u.clone());
      drop(borrow);
      let mut mut_borrow = thunk.borrow_mut();
      *mut_borrow = Thunk::Res(val.clone());
      val
    },
  }
}

pub fn eval(mut u: Comp) -> Value {
  match &*u.expr {
    Expr::Var(idx) => {
      force(u.e_env[*idx].clone())
    },
    Expr::Sort(lvl) => {
      // Value::Sort only takes fully reduced levels, so we instantiate all variables using the universe environment, then reduce it
      let lvl = reduce(&instantiate_univ_bulk(lvl, &u.u_env));
      Value::Sort(lvl)
    },
    Expr::Const(cnst, univs) => {
      let u_env = univs.iter().map(|lvl| {
	reduce(&instantiate_univ_bulk(lvl, &u.u_env))
      }).collect();
      eval_const(cnst, u_env)
    },
    Expr::App(fun, arg) => {
      let arg = suspend(Comp { expr: arg.clone(), ..u.clone() });
      let fun = eval(Comp { expr: fun.clone(), ..u.clone() });
      match fun {
	Value::Lam(_, body) => {
	  let mut body = body.clone();
	  body.e_env.push_front(arg);
	  eval(body)
	},
	Value::App(var@Neutral::FVar(..), args) => {
	  let mut args = args.clone();
	  args.push_front(arg);
	  Value::App(var, args)
	},
	Value::App(Neutral::Const(cnst, univs), args) => {
	  let u_env = univs.iter().map(|lvl| {
	    reduce(&instantiate_univ_bulk(lvl, &u.u_env))
	  }).collect();
	  apply_const(cnst, u_env, arg, args)
	},
	_ => unreachable!(),
      }
    },
    Expr::Lam(binfo, _, body) => {
      let body = Comp { expr: body.clone(), ..u };
      Value::Lam(*binfo, body)
    },
    Expr::Pi(binfo, dom, cod) => {
      let dom = Comp { expr: dom.clone(), ..u.clone() };
      let cod = Comp { expr: cod.clone(), ..u };
      Value::Pi(*binfo, suspend(dom), cod)
    },
    Expr::Let(_, expr, body) => {
      let expr = Comp { expr: expr.clone(), ..u.clone() };
      u.e_env.push_front(suspend(expr));
      let body = Comp { expr: body.clone(), ..u };
      eval(body)
    },
    Expr::Lit(lit) => Value::Lit(lit.clone()),
    Expr::Lty(lty) => Value::Lty(*lty),
    Expr::Fix(body) => {
      let mut unroll = Comp { expr: body.clone(), ..u.clone() };
      let itself = suspend(u);
      unroll.e_env.push_front(itself);
      eval(unroll)
    },
  }
}

pub fn eval_const(cnst: &ConstPtr, u_env: Vector<UnivPtr>) -> Value {
  match &**cnst {
    Const::Theorem { expr, ..} |
    Const::Definition { safe: DefSafety::Safe, expr, .. } => {
      eval(Comp { expr: expr.clone(), e_env: Vector::new(), u_env })
    },
    Const::Definition { safe: DefSafety::Unsafe, .. } => {
      panic!("Cannot use unsafe definitions inside types")
    },
    _ => {
      Value::App(Neutral::Const(cnst.clone(), u_env), Vector::new())
    },
  }
}

pub fn apply_const(cnst: ConstPtr, u_env: Vector<UnivPtr>, arg: ThunkPtr, mut args: Vector<ThunkPtr>) -> Value {
  // Assumes a partial application of k to args, which means in particular, that it is in normal form
  match &*cnst {
    Const::Recursor { params, motives, minors, indices, rules, ..} => {
      let major_idx = params + motives + minors + indices;
      if args.len() != major_idx {
	args.push_front(arg);
	return Value::App(Neutral::Const(cnst, u_env), args)
      }
      match force(arg.clone()) {
	Value::App(Neutral::Const(ctor, _), ctor_args) => {
	  match &*ctor {
	    Const::Constructor {..} => {
              // Since we assume expressions are previously type checked, we know that this constructor
              // must have an associated recursion rule
	      let rule = rules
		.get(&Rc::as_ptr(&ctor))
		.unwrap();
	      // Indices are not needed used at all in recursion rules
	      args.slice(indices ..);
              // The number of parameters in the constructor is not necessarily equal to the number of parameters in the recursor in nested
	      // inductive types, but the rule knows how many arguments to take
	      let mut e_env = ctor_args.take(rule.nfields);
	      e_env.append(args);
	      return eval(Comp { expr: rule.rhs.clone(), e_env, u_env })
	    }
	    _ => ()
	  }
	},
	_ => (),
      }
    }
    Const::Quotient {..} => {
      todo!()
    }
    _ => ()
  }
  args.push_front(arg);
  Value::App(Neutral::Const(cnst, u_env), args)
}
