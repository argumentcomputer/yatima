import Lean.Compiler.LCNF
import Batteries.Data.RBMap

open Batteries

namespace Lean.Compiler.LCNF

def LetValue.getUsedConstant : LetValue → RBSet Name cmp
  | .value _ | .erased | .proj .. | .fvar .. => .empty
  | .const declName .. => .single declName

partial def Code.getUsedConstants : Code → RBSet Name cmp
  | .let decl k => k.getUsedConstants.union decl.value.getUsedConstant
  | .fun decl k => k.getUsedConstants.union decl.value.getUsedConstants
  | .jp decl k => k.getUsedConstants.union decl.value.getUsedConstants
  | .cases cs => cs.alts.foldl (init := .empty) fun acc alt => acc.union alt.getCode.getUsedConstants
  | .jmp .. | .return _ | .unreach _ => .empty

def Decl.getUsedConstants (decl : Decl) : RBSet Name cmp :=
  let (name, type, value) := (decl.name, decl.type, decl.value)
  value.getUsedConstants.union (.ofArray type.getUsedConstants _) |>.insert name

def isGeneratedFrom (parent : Name) : Name → Bool
  | .str n s => n == parent &&
    -- TODO FIXME: these are hardcoded suffix values and are brittle
    -- but it works for now sooooo
    ("_lam_".isPrefixOf s || "_elam_".isPrefixOf s ||
     "spec_".isPrefixOf s || "_redArg" == s)
  | _ => false

end Lean.Compiler.LCNF
