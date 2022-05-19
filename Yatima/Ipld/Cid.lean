import Yatima.Ipld.Multihash

structure Cid where
  version : Nat
  codec: Nat
  hash: Multihash
  deriving BEq, Inhabited, Repr

namespace Cid

def toBytes (self : Cid) : ByteArray :=
  (UnsignedVarInt.toVarInt self.version)
    ++ (UnsignedVarInt.toVarInt self.codec)
    ++ (Multihash.toBytes self.hash)

def toString (self: Cid) : String :=
  Multibase.encode Multibase.Base32 (toBytes self).toList

instance : ToString Cid where
  toString := toString

def fromBytes (bytes : ByteArray) : Option Cid :=
  Option.bind (UnsignedVarInt.fromVarInt bytes) $ fun (version, bytes) =>
  Option.bind (UnsignedVarInt.fromVarInt bytes) $ fun (codec, bytes) =>
  Option.bind (Multihash.fromBytes bytes) $ fun hash =>
  some { version, codec, hash }

instance : Ord Cid where
  compare x y := compare x.toBytes y.toBytes

end Cid
