import YatimaStdLib.ByteVector

def ByteVector.repr (bv : ByteVector n) (prec : Nat) : Std.Format :=
  toString bv.data
where
  toString (bs : ByteArray) : String :=
    bs.data.foldl (init := "") fun acc byte => acc ++ (List.asString $ Nat.toDigits 16 byte.toNat)

instance : Repr (ByteVector n) where
  reprPrec := ByteVector.repr

namespace Yatima.IR

abbrev Hash := ByteVector 32

end Yatima.IR