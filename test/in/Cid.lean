import Yatima.Ipld.Cid

open Cid

def ex1' : Multihash := { code := 0x11, size := 0x4, digest := { data := #[0b10110110, 0b11111000, 0b01011100, 0b10110101] }}
def ex1 : Cid := { version := 0x1, codec := 0x11, hash := ex1' }

#eval ex1
#eval toBytes ex1
#eval fromBytes (toBytes ex1)
