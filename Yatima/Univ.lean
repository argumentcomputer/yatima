import Yatima.Cid
import Yatima.Name

namespace Yatima

inductive Univ (k : Kind) where
  | zero
  | succ  : UnivCid k → Univ k
  | max   : UnivCid k → UnivCid k → Univ k
  | imax  : UnivCid k → UnivCid k → Univ k
  | param : UnitIfAnon k Name → UnitIfMeta k Nat → Univ k
  -- deriving BEq, Inhabited
  deriving Inhabited

def Univ.toAnon : Univ .Pure → Univ .Anon
  | zero      => .zero
  | succ u    => .succ u.anon
  | max a b   => .max a.anon b.anon
  | imax a b  => .imax a.anon b.anon
  | param _ i => .param () i

def Univ.toMeta : Univ .Pure → Univ .Meta
  | zero      => .zero
  | succ u    => .succ u.meta
  | max a b   => .max a.meta b.meta
  | imax a b  => .imax a.meta b.meta
  | param n _ => .param n ()

end Yatima
