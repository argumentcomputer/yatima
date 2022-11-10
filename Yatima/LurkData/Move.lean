import Lurk.Field
import Lurk.Hashing.Encoding
import Lurk.SerDe.Deserialize

namespace Lurk.Syntax

namespace AST

/-- Uses Poseidon hashing
  TODO: This is extremely expensive -/
def hash (a : AST) : F := (commit a).1

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

-- namespace Lurk.SerDe

-- def deserialize (bytes : ByteArray) :
--     Except String ((List ScalarPtr) × ScalarStore) :=
--   (StateT.run (ReaderT.run deserializeM ⟨bytes, bytes.size, by eq_refl⟩) 0).1

-- end Lurk.SerDe
