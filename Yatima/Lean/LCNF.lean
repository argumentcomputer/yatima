import Lean.Compiler.LCNF
import Lean.Util.FoldConsts
import Std.Data.RBMap

open Std

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
    ("_lam_".isPrefixOf s || "_elam_".isPrefixOf s || 
    "spec_".isPrefixOf s || "_redArg" == s)
  | _ => false

def findCore (env : Environment) (ext : DeclExt) (ϕ : Decl → Bool) : Array Decl :=
  ext.getState env |>.foldl (init := #[]) fun acc _ decl =>
    if ϕ decl then
      acc.push decl
    else
      acc

def test : MetaM Unit := do
  -- let decls := findCore (← getEnv) monoExt fun decl => (``List.map) == decl.name
  IO.println $ monoExt.getState (← getEnv) |>.toList.map Prod.fst
  -- IO.println $ decls.map (·.name)

#eval test


end Lean.Compiler.LCNF