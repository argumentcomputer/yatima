import Yatima.Cid
import Yatima.Name

namespace Yatima

inductive Univ where
  | zero
  | succ  : UnivCid → Univ
  | max   : UnivCid → UnivCid → Univ
  | imax  : UnivCid → UnivCid → Univ
  | param : Name → Nat → Univ
  deriving BEq, Inhabited

inductive UnivAnon where
  | zero
  | succ  : UnivAnonCid → UnivAnon
  | max   : UnivAnonCid → UnivAnonCid → UnivAnon
  | imax  : UnivAnonCid → UnivAnonCid → UnivAnon
  | param : Nat → UnivAnon
  deriving BEq, Inhabited

inductive UnivMeta where
  | zero
  | succ  : UnivMetaCid → UnivMeta
  | max   : UnivMetaCid → UnivMetaCid → UnivMeta
  | imax  : UnivMetaCid → UnivMetaCid → UnivMeta
  | param : Name → UnivMeta
  deriving BEq, Inhabited

def Univ.toAnon : Univ → UnivAnon
  | zero      => .zero
  | succ u    => .succ u.anon
  | max a b   => .max a.anon b.anon
  | imax a b  => .imax a.anon b.anon
  | param _ i => .param i

def Univ.toMeta : Univ → UnivMeta
  | zero      => .zero
  | succ u    => .succ u.meta
  | max a b   => .max a.meta b.meta
  | imax a b  => .imax a.meta b.meta
  | param n _ => .param n

end Yatima
