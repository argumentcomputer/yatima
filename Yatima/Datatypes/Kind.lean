import Yatima.Datatypes.Lean

namespace Yatima.Ipld

/--
Used to indicate whether a `Yatima.Split` refers to an attribute of an anon or
meta `Ipld.Univ`/`Ipld.Expr`/`Ipld.Const`.
-/
inductive Kind where
  | anon : Kind
  | meta : Kind
  deriving BEq, Inhabited

instance : Coe Kind Bool where coe
  | .anon => true
  | .meta => false

end Yatima.Ipld
