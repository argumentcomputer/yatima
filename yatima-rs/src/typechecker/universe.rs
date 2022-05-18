use std::rc::Rc;

pub type UnivPtr = Rc<Univ>;

/// Indexes are used for environment lookups. They take place of de Bruijn indices or levels.
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

// Reduce, or simplify, the universes to a normal form
pub fn reduce(univ: &UnivPtr) -> UnivPtr {
  match &**univ {
    Univ::Succ(a) => {
      Rc::new(Univ::Succ(reduce(a)))
    }
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
    _ => univ.clone()
  }
}

// Instantiate a variable and reduce at the same time. Assumes an already reduced `subst`
pub fn inst_reduce(univ: &UnivPtr, idx: Index, subst: &UnivPtr) -> UnivPtr {
  match &**univ {
    Univ::Succ(a) => {
      Rc::new(Univ::Succ(inst_reduce(a, idx, subst)))
    }
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
      if *jdx < idx {
	univ.clone()
      }
      else if *jdx > idx {
	Rc::new(Univ::Var(*jdx-1))
      }
      else {
	subst.clone()
      }
    }
    Univ::Zero => univ.clone(),
  }
}

// Instantiate multiple variables at the same time and reduce. Assumes already reduced `substs`
pub fn inst_bulk_reduce(univ: &UnivPtr, substs: &Vector<UnivPtr>) -> UnivPtr {
  match &**univ {
    Univ::Succ(a) => {
      Rc::new(Univ::Succ(inst_bulk_reduce(a, substs)))
    }
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
	Rc::new(Univ::Var(*jdx - substs.len()))
      }
    }
    Univ::Zero => univ.clone(),
  }
}

// Assumes univ_a and univ_b are already reduced
pub fn reduce_max(univ_a: &UnivPtr, univ_b: &UnivPtr) -> UnivPtr {
  match (&**univ_a, &**univ_b) {
    (Univ::Zero, _) => univ_b.clone(),
    (_, Univ::Zero) => univ_a.clone(),
    (Univ::Succ(univ_a), Univ::Succ(univ_b)) => {
      Rc::new(Univ::Succ(reduce_max(univ_a, univ_b)))
    },
    _ => Rc::new(Univ::Max(univ_a.clone(), univ_b.clone()))
  }
}

pub enum Comp {
  // Means we know `a` is equal `b`
  Equal,
  // Means `a` is not greater than `b`, but we can't know whether they are (happens in presence of free universe variables)
  LessOr,
  // Any other case, be it unknown or `a` is greater than `b`
  Else,
}

// Assumes `a` and `b` are already reduced
pub fn equal_univ(a: &UnivPtr, b: &UnivPtr) -> bool {
  match comp_univ(&a, &b, 0) {
    Comp::Equal => true,
    _ => false
  }
}

// Compares `a` with `a + diff`, whatever `a` is
pub fn diff_comp(diff: i64) -> Comp {
  if diff > 0 {
    return Comp::LessOr
  }
  if diff < 0 {
    return Comp::Else
  }
  return Comp::Equal
}

pub fn comp_univ(a: &UnivPtr, b: &UnivPtr, diff: i64) -> Comp {
  // Shortcut
  if Rc::as_ptr(a) == Rc::as_ptr(b) {
    return diff_comp(diff)
  }
  match (&**a, &**b) {
    (Univ::Zero, Univ::Zero) => diff_comp(diff),
    (Univ::Succ(a), _) => comp_univ(a, b, diff-1),
    (_, Univ::Succ(b)) => comp_univ(a, b, diff+1),
    (Univ::Zero, _) if diff >= 0 => Comp::LessOr,
    (Univ::Zero, Univ::Var(_)) => Comp::Else, // note that `diff < 0` here
    (_, Univ::Zero) => Comp::Else, // can be proven by induction
    (Univ::Var(idx), Univ::Var(jdx)) => {
      if idx != jdx {
	return Comp::Else
      }
      diff_comp(diff)
    },
    (Univ::Max(c, d), _) => {
      match comp_univ(c, b, diff) {
	Comp::Else => Comp::Else,
	Comp::Equal => {
	  match comp_univ(d, b, diff) {
	    Comp::Else => Comp::Else,
	    _ => Comp::Equal
	  }
	}
	Comp::LessOr => {
	  match comp_univ(d, b, diff) {
	    Comp::Else => Comp::Else,
	    Comp::Equal => Comp::Equal,
	    Comp::LessOr => Comp::LessOr
	  }
	}
      }
    },
    (_, Univ::Max(c, d)) => {
      match comp_univ(c, a, diff) {
	Comp::Else => Comp::Else,
	Comp::Equal => {
	  match comp_univ(d, a, diff) {
	    Comp::Else => Comp::Else,
	    _ => Comp::Equal
	  }
	}
	Comp::LessOr => {
	  match comp_univ(d, a, diff) {
	    Comp::Else => Comp::Else,
	    Comp::Equal => Comp::Equal,
	    Comp::LessOr => Comp::LessOr
	  }
	}
      }
    },
    (Univ::IMax(..), _) => {
      todo!()
    },
    (_, Univ::IMax(..)) => {
      todo!()
    },
  }
}

// Faster equality for zero, assumes reduced `a`
pub fn univ_is_zero(a: &UnivPtr) -> bool {
  match &**a {
    Univ::Zero => true,
    _ => false, // all other cases are false since they are either `Succ` or a stuck computation
  }
}
