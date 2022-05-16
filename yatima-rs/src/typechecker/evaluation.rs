use crate::{
  typechecker::expression::*,
  typechecker::value::*,
};
use std::rc::Rc;
use std::cell::RefCell;

pub fn freeze(u: Comp) -> ThunkPtr {
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
      force(u.e_env[*idx as usize].clone())
    },
    Expr::Sort(lvl) => Value::Sort(lvl.clone()),
    Expr::Const(..) => todo!(),
    Expr::App(fun, arg) => {
      let arg = freeze(Comp { expr: arg.clone(), ..u.clone() });
      let fun = eval(Comp { expr: fun.clone(), ..u });
      match fun {
	Value::Lam(_, body) => {
	  let mut body = body.clone();
	  body.e_env.push_front(arg);
	  eval(body)
	},
	Value::App(var@Neutral::FVar(..), args) => {
	  let mut args = args.clone();
	  args.push_back(arg);
	  Value::App(var, args)
	},
	Value::App(Neutral::Const(..), ..) => {
	  panic!()
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
      Value::Pi(*binfo, freeze(dom), cod)
    },
    Expr::Let(_, expr, body) => {
      let expr = Comp { expr: expr.clone(), ..u.clone() };
      u.e_env.push_front(freeze(expr));
      let body = Comp { expr: body.clone(), ..u };
      eval(body)
    },
    Expr::Lit(lit) => Value::Lit(lit.clone()),
    Expr::Lty(lty) => Value::Lty(*lty),
    Expr::Fix(body) => {
      let mut unroll = Comp { expr: body.clone(), ..u.clone() };
      let itself = freeze(u);
      unroll.e_env.push_front(itself);
      eval(unroll)
    },
  }
}
