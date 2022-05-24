use std::rc::Rc;

pub type UnivPtr = Rc<Univ>;

/// Indexes are used for environment lookups. They take place of de Bruijn
/// indices or levels.
pub type Index = usize;

use im::Vector;

/// Universe levels
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Univ {
  /// Sort 0 aka Prop
  Zero,
  /// Sort (n + 1)
  Succ(UnivPtr),
  /// Sort (max u v)
  Max(UnivPtr, UnivPtr),
  /// Sort (imax u v)
  IMax(UnivPtr, UnivPtr),
  /// Sort u
  Var(Index),
}

// Reduce, or simplify, the universe levels to a normal form. Notice that
// universe levels with no free variables always reduce to a number,
// i.e., a sequence of `Succ`s followed by a `Zero`
pub fn reduce(univ: &UnivPtr) -> UnivPtr {
  match &**univ {
    Univ::Succ(a) => Rc::new(Univ::Succ(reduce(a))),
    Univ::Max(a, b) => {
      let a = reduce(a);
      let b = reduce(b);
      reduce_max(&a, &b)
    }
    Univ::IMax(a, b) => {
      let b = reduce(b);
      match &*b {
        // IMax(a, b) will reduce to 0 if b == 0
        Univ::Zero => b,
        // IMax(a, b) will reduce as Max(a, b) if b == Succ(..)
        Univ::Succ(..) => {
          let a = reduce(a);
          reduce_max(&a, &b)
        }
        // Otherwise, IMax(a, b) is stuck, with a and b reduced
        _ => {
          let a = reduce(a);
          Rc::new(Univ::IMax(a, b))
        }
      }
    }
    _ => univ.clone(),
  }
}

// Instantiate a variable and reduce at the same time. Assumes an already
// reduced `subst` This function is only used in the comparison algorithm, and
// it doesn't shift variables, because we want to instantiate a variable
// Var(idx) with Succ(Var(idx)), so by shifting the variables we would transform
// Var(idx+1) into Var(idx), which is not what we want
pub fn inst_reduce(univ: &UnivPtr, idx: Index, subst: &UnivPtr) -> UnivPtr {
  match &**univ {
    Univ::Succ(a) => Rc::new(Univ::Succ(inst_reduce(a, idx, subst))),
    Univ::Max(a, b) => {
      let a = inst_reduce(a, idx, subst);
      let b = inst_reduce(b, idx, subst);
      reduce_max(&a, &b)
    }
    Univ::IMax(a, b) => {
      let b = inst_reduce(b, idx, subst);
      match &*b {
        // IMax(a, b) will reduce to 0 if b == 0
        Univ::Zero => b,
        // IMax(a, b) will reduce as Max(a, b) if b == Succ(..)
        Univ::Succ(..) => {
          let a = inst_reduce(a, idx, subst);
          reduce_max(&a, &b)
        }
        // Otherwise, IMax(a, b) is stuck, with a and b reduced
        _ => {
          let a = inst_reduce(a, idx, subst);
          Rc::new(Univ::IMax(a, b))
        }
      }
    }
    Univ::Var(jdx) => {
      if *jdx == idx {
        subst.clone()
      }
      else {
        univ.clone()
      }
    }
    Univ::Zero => univ.clone(),
  }
}

// Instantiate multiple variables at the same time and reduce. Assumes already
// reduced `substs`
pub fn inst_bulk_reduce(univ: &UnivPtr, substs: &Vector<UnivPtr>) -> UnivPtr {
  match &**univ {
    Univ::Succ(a) => Rc::new(Univ::Succ(inst_bulk_reduce(a, substs))),
    Univ::Max(a, b) => {
      let a = inst_bulk_reduce(a, substs);
      let b = inst_bulk_reduce(b, substs);
      reduce_max(&a, &b)
    }
    Univ::IMax(a, b) => {
      let b = inst_bulk_reduce(b, substs);
      match &*b {
        // IMax(a, b) will reduce to 0 if b == 0
        Univ::Zero => b,
        // IMax(a, b) will reduce as Max(a, b) if b == Succ(..)
        Univ::Succ(..) => {
          let a = inst_bulk_reduce(a, substs);
          reduce_max(&a, &b)
        }
        // Otherwise, IMax(a, b) is stuck, with a and b reduced
        _ => {
          let a = inst_bulk_reduce(a, substs);
          Rc::new(Univ::IMax(a, b))
        }
      }
    }
    Univ::Var(jdx) => {
      if (*jdx as usize) < substs.len() {
        substs[*jdx as usize].clone()
      }
      else {
        // TODO: It is still unclear, at this point, whether we should shift or
        // not the other variables. In fact, it is still unclear whether
        // this case could happen at all. It would appear that the `substs`
        // variable is a complete environment for the free variables
        // inside `univ`
        Rc::new(Univ::Var(*jdx - substs.len()))
      }
    }
    Univ::Zero => univ.clone(),
  }
}

// Reduces as a `Max` applied to two values; so max(a,0) = max(0,a) = a and
// max(succ(a),succ(b)) = succ(max(a,b)). It is assumed that `univ_a` and
// `univ_b` are already reduced
pub fn reduce_max(univ_a: &UnivPtr, univ_b: &UnivPtr) -> UnivPtr {
  match (&**univ_a, &**univ_b) {
    (Univ::Zero, _) => univ_b.clone(),
    (_, Univ::Zero) => univ_a.clone(),
    (Univ::Succ(univ_a), Univ::Succ(univ_b)) => {
      Rc::new(Univ::Succ(reduce_max(univ_a, univ_b)))
    }
    _ => Rc::new(Univ::Max(univ_a.clone(), univ_b.clone())),
  }
}

/// Equality
// We say that two universe levels `a` and `b` are (semantically) equal, if they
// are equal as numbers for all possible substitution of free variables to
// numbers. Although writing an algorithm that follows this exact scheme is
// impossible, it is possible to write one that is equivalent to such semantical
// equality.

// The equality algorithm. Assumes `a` and `b` are already reduced
#[inline]
pub fn equal_univ(a: &UnivPtr, b: &UnivPtr) -> bool {
  leq_univ(a, b, 0) && leq_univ(b, a, 0)
}

// Comparison algorithm `a <= b + diff`. Assumes `a` and `b` are already reduced
pub fn leq_univ(a: &UnivPtr, b: &UnivPtr, diff: i64) -> bool {
  // Shortcut
  if Rc::as_ptr(a) == Rc::as_ptr(b) {
    return diff >= 0;
  }
  match (&**a, &**b) {
    // Zero, Succ, and Var cases
    (Univ::Zero, Univ::Zero) => diff >= 0,
    (Univ::Zero, _) if diff >= 0 => true,
    (_, Univ::Zero) if diff < 0 => false,
    (Univ::Var(_), Univ::Zero) => false,
    (Univ::Zero, Univ::Var(_)) => false,
    (Univ::Var(idx), Univ::Var(jdx)) => idx == jdx && diff >= 0,
    (Univ::Succ(a), _) => leq_univ(a, b, diff - 1),
    (_, Univ::Succ(b)) => leq_univ(a, b, diff + 1),

    // Max cases
    (Univ::Max(c, d), _) => leq_univ(c, b, diff) && leq_univ(d, b, diff),
    (_, Univ::Max(c, d)) => leq_univ(a, c, diff) || leq_univ(a, d, diff),

    // IMax cases
    (Univ::IMax(c, d), _) => {
      // The case a = IMax(c,d) has only three possibilities:
      // - d = Var(..)
      // - d = Max(..)
      // - d = IMax(..)
      // It can't be any otherway since we are assuming a is reduced, and thus d
      // is reduced as well
      match &**d {
        Univ::Var(idx) => {
          // In the case for Var(idx), we need to compare two substitutions:
          // -- idx <- Zero
          // -- idx <- Succ(Var(idx))
          // The first substitution, where we know `a` becomes Zero
          let zero = Rc::new(Univ::Zero);
          let subst_b1 = inst_reduce(b, *idx, &zero);
          if leq_univ(&zero, &subst_b1, diff) {
            // The second substitution
            let succ = Rc::new(Univ::Succ(d.clone()));
            let subst_a2 = inst_reduce(a, *idx, &succ);
            let subst_b2 = inst_reduce(b, *idx, &succ);
            return leq_univ(&subst_a2, &subst_b2, diff);
          }
          false
        }
        Univ::Max(e, f) => {
          // Here we use the relationship
          // IMax(c, Max(e,f)) = Max(IMax(c,e), IMax(c,f))
          let new_a = Rc::new(Univ::Max(
            Rc::new(Univ::IMax(c.clone(), e.clone())),
            Rc::new(Univ::IMax(c.clone(), f.clone())),
          ));
          leq_univ(&reduce(&new_a), b, diff)
        }
        Univ::IMax(e, f) => {
          // Here we use the relationship
          // IMax(c, IMax(e,f)) = Max(IMax(c,e), IMax(e,f))
          let new_a = Rc::new(Univ::Max(
            Rc::new(Univ::IMax(c.clone(), e.clone())),
            Rc::new(Univ::IMax(e.clone(), f.clone())),
          ));
          leq_univ(&reduce(&new_a), b, diff)
        }
        _ => unreachable!(),
      }
    }
    (_, Univ::IMax(c, d)) => {
      // Analogous to previous case
      match &**d {
        Univ::Var(idx) => {
          let zero = Rc::new(Univ::Zero);
          let subst_a1 = inst_reduce(b, *idx, &zero);
          if leq_univ(&subst_a1, &zero, diff) {
            let succ = Rc::new(Univ::Succ(d.clone()));
            let subst_a2 = inst_reduce(a, *idx, &succ);
            let subst_b2 = inst_reduce(b, *idx, &succ);
            return leq_univ(&subst_a2, &subst_b2, diff);
          }
          false
        }
        Univ::Max(e, f) => {
          let new_b = Rc::new(Univ::Max(
            Rc::new(Univ::IMax(c.clone(), e.clone())),
            Rc::new(Univ::IMax(c.clone(), f.clone())),
          ));
          leq_univ(a, &reduce(&new_b), diff)
        }
        Univ::IMax(e, f) => {
          let new_b = Rc::new(Univ::Max(
            Rc::new(Univ::IMax(c.clone(), e.clone())),
            Rc::new(Univ::IMax(e.clone(), f.clone())),
          ));
          leq_univ(a, &reduce(&new_b), diff)
        }
        _ => unreachable!(),
      }
    }
  }
}

// Faster equality for zero, assumes reduced `a`
#[inline]
pub fn univ_is_zero(a: &UnivPtr) -> bool {
  match &**a {
    Univ::Zero => true,
    // all other cases are false since they are either `Succ` or a reduced
    // expression with free variables, which are never semantically equal to
    // zero
    _ => false,
  }
}
