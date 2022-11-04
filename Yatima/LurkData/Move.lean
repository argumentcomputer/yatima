import Lurk.Field
import Lurk.Syntax.AST

namespace Lurk.Syntax

namespace AST

/-- Uses Poseidon hashing -/
def hash : AST → F
  | _ => sorry

def f   (n : Fin N)  : AST := .num n
def u8    (n : UInt8)  : AST := .num n.val
def u16   (n : UInt16) : AST := .num n.val
def u32   (n : UInt32) : AST := .num n.val
def u64   (n : UInt64) : AST := .num n.val
def usize (n : USize)  : AST := .num n.val

@[match_pattern] def t : AST := .sym "T"
@[match_pattern] def comm : AST := .sym "COMM"

end AST

namespace ToAST

instance : ToAST AST where
  toAST a := a

end ToAST

end Lurk.Syntax
