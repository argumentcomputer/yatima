namespace Yatima

inductive Kind where
| Pure : Kind
| Anon : Kind
| Meta : Kind
deriving BEq, Inhabited

macro "kindEtaExpand" k:term "with" x:term : term =>
  `(match $k:term with | .Pure => $x:term | .Anon => $x:term | .Meta => $x:term)

def substIfAnon : Kind → A → A → A
| .Anon, a, _ => a
| _, _, b => b

def UnitIfAnon : Kind → Type → Type
| .Anon, _ => Unit
| _, A => A

def UnitIfMeta : Kind → Type → Type
| .Meta, _ => Unit
| _, A => A

end Yatima
