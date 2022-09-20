import Yatima.Ipld.ToIpld
import Yatima.Datatypes.Univ

open Yatima Ipld ToIpld
def univ := @Univ.zero Kind.anon
def univCtor := univToIpld univ