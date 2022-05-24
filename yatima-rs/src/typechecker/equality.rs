use crate::typechecker::{
  evaluation::*,
  universe::*,
  value::*,
};
use im::Vector;
use std::rc::Rc;

#[inline]
pub fn extend_with_thunk(mut env: Env, thunk: ThunkPtr) -> Env {
  env.exprs.push_back(thunk);
  env
}

#[inline]
pub fn new_var(idx: Index) -> Value {
  Value::App(Neutral::FVar(idx), Vector::new())
}

// Equality conversion algorithm between two *well-typed* values with the same
// type
pub fn equal(a: &Value, b: &Value, dep: Index) -> bool {
  // Short circuit if they're the same pointer
  if a as *const Value == b as *const Value {
    return true;
  }
  // TODO: Return true if they are proof irrelevant terms or are elements of a
  // unit type
  match (a, b) {
    (Value::Sort(a_univ), Value::Sort(b_univ)) => equal_univ(a_univ, b_univ),
    (Value::App(a_neu, a_args), Value::App(b_neu, b_args)) => {
      match (a_neu, b_neu) {
        (Neutral::FVar(a_idx), Neutral::FVar(b_idx)) => {
          a_idx == b_idx && equal_args(a_args, b_args, dep)
        }
        (Neutral::Const(a_cnst, _), Neutral::Const(b_cnst, _)) =>
        // Univs should be equal since they have the same type. Also, because of
        // CID <-> Pointer correspondence, we need only check for
        // pointer equality of constants
        {
          Rc::as_ptr(a_cnst) == Rc::as_ptr(b_cnst)
            && equal_args(a_args, b_args, dep)
        }
        _ => false,
      }
    }
    (Value::Lam(a_inf, a_bod, a_env), Value::Lam(b_inf, b_bod, b_env)) => {
      if a_inf != b_inf {
        return false;
      }
      let new_var = result(new_var(dep));
      let a = Rc::new(eval(
        a_bod.clone(),
        extend_with_thunk(a_env.clone(), new_var.clone()),
      ));
      let b =
        Rc::new(eval(b_bod.clone(), extend_with_thunk(b_env.clone(), new_var)));
      equal(&a, &b, dep + 1)
    }
    (
      Value::Pi(a_inf, a_dom, a_img, a_env),
      Value::Pi(b_inf, b_dom, b_img, b_env),
    ) => {
      if a_inf != b_inf || !equal(&force(a_dom), &force(b_dom), dep) {
        return false;
      }
      let new_var = result(new_var(dep));
      let a = Rc::new(eval(
        a_img.clone(),
        extend_with_thunk(a_env.clone(), new_var.clone()),
      ));
      let b =
        Rc::new(eval(b_img.clone(), extend_with_thunk(b_env.clone(), new_var)));
      equal(&a, &b, dep + 1)
    }
    (Value::Lit(a_lit), Value::Lit(b_lit)) => a_lit == b_lit,
    (Value::Lty(a_lty), Value::Lty(b_lty)) => a_lty == b_lty,
    _ => false,
  }
}

#[inline]
pub fn equal_args(
  a_args: &Vector<ThunkPtr>,
  b_args: &Vector<ThunkPtr>,
  dep: Index,
) -> bool {
  if a_args != b_args {
    return false;
  }
  for i in 0..a_args.len() {
    if !equal(&force(&a_args[i]), &force(&b_args[i]), dep) {
      return false;
    }
  }
  true
}
