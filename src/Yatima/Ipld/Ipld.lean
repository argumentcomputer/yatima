import Yatima.Ipld.Cid
import Yatima.Ipld.Multihash
import Yatima.Ipld.Utils
import Std.Data.RBTree

open Std (RBNode)

def toList (map : RBNode α (fun _ => β)) : List (α × β) :=
  map.revFold (fun as a b => (a,b)::as) []

instance [BEq α] [BEq β] : BEq (RBNode α fun _ => β) where
  beq a b := toList a == toList b

instance : BEq Cid where
  beq a b := a.version == b.version && a.codec == b.codec && a.hash == b.hash

inductive Ipld where
  | null
  | bool (b : Bool)
  | number (n : UInt64)
  | string (s : String)
  | bytes (b : ByteArray)
  | array (elems : Array Ipld)
  | object (kvPairs : RBNode String (fun _ => Ipld))
  | link (cid: Cid)
  deriving BEq, Inhabited

instance : Repr Ipld where
  reprPrec
  | Ipld.null, prec => Repr.addAppParen ("Ipld.null") prec
  | Ipld.bool b, prec => Repr.addAppParen ("Ipld.bool " ++ toString b) prec
  | Ipld.number n, prec => Repr.addAppParen ("Ipld.number " ++ toString n) prec
  | Ipld.string n, prec => Repr.addAppParen ("Ipld.string " ++ toString n) prec
  | Ipld.bytes n, prec => Repr.addAppParen ("Ipld.bytes " ++ toString n) prec
  | Ipld.link n, prec => Repr.addAppParen ("Ipld.link " ++ toString n) prec
  --| Ipld.array n, prec => Repr.addAppParen ("Ipld.array " ++ reprPrec n.data prec) prec
  | _, prec => Repr.addAppParen ("Ipld.todo") prec

--def Ipld.toStringAux : Ipld → String
--| Ipld.null =>  "Ipld.null" 
--| Ipld.bool b  =>  "Ipld.bool " ++ toString b 
--| Ipld.number n  =>  "Ipld.number " ++ toString n 
--| Ipld.string n  =>  "Ipld.string " ++ toString n 
--| Ipld.byte n  =>  "Ipld.byte " ++ toString n 
----| Ipld.array n  =>  "Ipld.array " ++ n.data
--| _  =>  "Ipld.todo" 
--
--instance : ToString Ipld where
--   toString := Ipld.toStringAux

def Ipld.mkObject (o : List (String × Ipld)) : Ipld :=
  object $ o.foldl (init := RBNode.leaf)
    fun acc (k, v) => acc.insert compare k v
