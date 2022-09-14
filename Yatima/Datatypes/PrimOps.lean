import Yatima.Datatypes.Const

namespace Yatima

open Std (RBMap)

opaque NatHash     : String := "bagcyb6egbqlcbvcn3yk3eojuobxafm2yn42oyux6im7vkcwrx7zykci56kwbt6pm"
opaque NatSuccHash : String := "bagcyb6egbqlcbop4tscfzg2s3eb7cfprycbn2r2oufqqmcg4uf5vcsqcp75fkeuh"
opaque NatAddHash  : String := "bagcyb6egbqlcbzfrbhy3it4b4uwk4cs5t3exu3toc7ku2asb5zwwhfbw43cf2rbb"
opaque NatBEqHash  : String := "bagcyb6egbqlcbyf4muoxoxo3l5t6gdy5ceuq4lxg6urx2y4bz2ovsiafxatqcn7i"
opaque NatBLeHash  : String := "bagcyb6egbqlcbfbhsruhszwv3mes6j3bpfgk6uvwka3abuxowhgme6ndp6o7vftg"
opaque NatSubHash  : String := "bagcyb6egbqlcazg4kka7vznpnpq36ank2z3w6zluomlnyjttccd37tb5ofvj6ni7"
opaque NatDivHash  : String := "bagcyb6egbqlcblsr5wjhbpbwa4cliik2qfh6brh76ddjczhtfch3vyelkbfisynr"
opaque NatModHash  : String := "bagcyb6egbqlcbmsy5qeqz5ojctrn2qflcqpx6bvjhspn52mjn2kegsvgll5hleef"
opaque NatMulHash  : String := "bagcyb6egbqlcbrwzmfpjtm7kqnxhq7q65fcukopureotdduj4ouiuatr4lbo2bc2"
opaque StringHash  : String := "bagcyb6egbqlcb4zsubwj2w2ygvvertlfc32ntomotqqcx5db25ewy7s73oo3n4ig"

def primOpMap : RBMap (Ipld.ConstCid Ipld.Kind.anon) Const compare :=
  default

end Yatima
