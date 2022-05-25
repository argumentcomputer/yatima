import Yatima.Ipld.UnsignedVarInt
import Yatima.Ipld.Multibase
import Yatima.Ipld.Keccak

instance : Repr ByteArray where
  reprPrec x prec := Repr.addAppParen ("ByteArray " ++ toString x.data) prec

structure Multihash where
  code : Nat
  size : Nat
  digest : ByteArray
  deriving BEq, Inhabited, Repr

namespace Yatima.Multihash

def toBytes (self : Multihash) : ByteArray :=
  (UnsignedVarInt.toVarInt self.code) ++ (UnsignedVarInt.toVarInt self.size) ++ self.digest

def toString (self: Multihash) : String :=
  Multibase.encode Multibase.Base64 (toBytes self).toList

instance : ToString Multihash where
  toString := toString

def fromBytes (bytes : ByteArray) : Option Multihash :=
  Option.bind (UnsignedVarInt.fromVarInt bytes) $ fun (code, bytes) =>
  Option.bind (UnsignedVarInt.fromVarInt bytes) $ fun (size, bytes) =>
  let digest := bytes
  if digest.size > size then none
  else some { code, size, digest }

def sha3_256 (x: ByteArray) : Multihash :=
  { code := 0x16, size := 32, digest := Keccak.sha3_256 x }

def sha3_512 (x: ByteArray) : Multihash :=
  { code := 0x14, size := 64, digest := Keccak.sha3_512 x }

end Yatima.Multihash
