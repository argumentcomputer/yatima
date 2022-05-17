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

pub fn instantiate_univ(univ: &UnivPtr, idx: Index, subst: &UnivPtr) -> UnivPtr {
  match &**univ {
    Univ::Zero => univ.clone(),
    Univ::Succ(a) => {
      Rc::new(Univ::Succ(instantiate_univ(a, idx, subst)))
    }
    Univ::Max(a, b) => {
      let a = instantiate_univ(a, idx, subst);
      let b = instantiate_univ(b, idx, subst);
      Rc::new(Univ::Max(a, b))
    }
    Univ::IMax(a, b) => {
      let a = instantiate_univ(a, idx, subst);
      let b = instantiate_univ(b, idx, subst);
      Rc::new(Univ::IMax(a, b))
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
  }
}

pub fn instantiate_univ_bulk(univ: &UnivPtr, substs: &Vector<UnivPtr>) -> UnivPtr {
  match &**univ {
    Univ::Zero => univ.clone(),
    Univ::Succ(a) => {
      Rc::new(Univ::Succ(instantiate_univ_bulk(a, substs)))
    }
    Univ::Max(a, b) => {
      let a = instantiate_univ_bulk(a, substs);
      let b = instantiate_univ_bulk(b, substs);
      Rc::new(Univ::Max(a, b))
    }
    Univ::IMax(a, b) => {
      let a = instantiate_univ_bulk(a, substs);
      let b = instantiate_univ_bulk(b, substs);
      Rc::new(Univ::IMax(a, b))
    }
    Univ::Var(jdx) => {
      if (*jdx as usize) < substs.len() {
	substs[*jdx as usize].clone()
      }
      else {
	Rc::new(Univ::Var(*jdx - substs.len()))
      }
    }
  }
}

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

pub fn reduce_max(univ_a: &UnivPtr, univ_b: &UnivPtr) -> UnivPtr {
  // Assumes univ_a and univ_b are already reduced
  match (&**univ_a, &**univ_b) {
    (Univ::Zero, _) => univ_b.clone(),
    (_, Univ::Zero) => univ_a.clone(),
    (Univ::Succ(univ_a), Univ::Succ(univ_b)) => reduce_max(univ_a, univ_b),
    _ => Rc::new(Univ::Max(univ_a.clone(), univ_b.clone()))
  }
}
