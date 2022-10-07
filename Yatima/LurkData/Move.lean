import Lurk.AST

namespace Lurk

namespace Expr

/-- Uses Poseidon hashing -/
def hash : Expr → Fin N
  | _ => sorry

def num   (n : Fin N)  : Lurk.Expr := .lit $ .num n
def nat   (n : Nat)    : Lurk.Expr := .lit $ .num (Fin.ofNat n)
def int   (n : Fin N)  : Lurk.Expr := .lit $ .num (Fin.ofInt n)
def u8    (n : UInt8)  : Lurk.Expr := nat n.val
def u16   (n : UInt16) : Lurk.Expr := nat n.val
def u32   (n : UInt32) : Lurk.Expr := nat n.val
def u64   (n : UInt64) : Lurk.Expr := nat n.val
def usize (n : USize)  : Lurk.Expr := nat n.val

end Expr

end Lurk
