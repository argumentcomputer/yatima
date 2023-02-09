import YatimaStdLib.ByteVector

namespace Yatima.IR

abbrev Hash := ByteVector 32

def Hash.repr (hash : Hash) (prec : Nat) : Std.Format :=
  toString hash.data
where
  toString (bs : ByteArray) : String :=
    bs.data.foldl (init := "") fun acc byte => acc ++ (List.asString $ Nat.toDigits 16 byte.toNat)

instance : Repr Hash where
  reprPrec := Hash.repr

end Yatima.IR