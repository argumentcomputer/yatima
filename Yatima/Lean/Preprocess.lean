import Lean
import Std.Lean.TagAttribute

namespace Lean

abbrev VisitM := ReaderT ConstMap $ StateM NameSet

namespace VisitM

def visited (c : Name) : VisitM Bool := do
  if (← get).contains c then
    return true
  else 
    modify fun s => s.insert c
    return false

partial def visit (c : Name) : VisitM Unit := do
  if ← visited c then
    return
  let consts := match (← read).find? c with
    | some (.defnInfo x) | some (.opaqueInfo x) | some (.thmInfo x) => 
      x.type.getUsedConstants ++ x.value.getUsedConstants
    | some (.axiomInfo x) | some (.quotInfo x) => x.type.getUsedConstants
    | some (.ctorInfo x) => x.type.getUsedConstants.push x.induct
    | some (.recInfo x) => x.type.getUsedConstants ++ x.all
    | some (.inductInfo x) => x.type.getUsedConstants ++ x.ctors ++ x.all
    | none => #[]
  for name in consts do
    visit name

def visitAll (cs : Array Name) : VisitM Unit := do
  for c in cs do visit c

end VisitM

def visitAll (constants : ConstMap) (cs : Array Name) : NameSet :=
  let (_, res) := (VisitM.visitAll cs).run constants |>.run .empty
  res

/-- Unfortunately must be hard coded -/
def visitComputedFields (env : Environment) : NameSet :=
  let decls := Elab.ComputedFields.computedFieldAttr.getDecls env
  let decls := decls ++ decls.map fun decl => decl ++ `_override
  visitAll env.constants decls

namespace Compiler.LCNF

def LetValue.getUsedConstant : LetValue → Array Name
  | .value _ | .erased | .proj .. | .fvar .. => #[]
  | .const declName .. => #[declName]  

partial def Code.getUsedConstants : Code → Array Name
  | .let decl k => k.getUsedConstants ++ decl.value.getUsedConstant
  | .fun decl k => k.getUsedConstants ++ decl.value.getUsedConstants
  | .jp decl k => k.getUsedConstants ++ decl.value.getUsedConstants
  | .cases cs => cs.alts.concatMap fun alt => alt.getCode.getUsedConstants
  | .jmp .. | .return _ | .unreach _ => #[]

def Decl.getUsedConstants (decl : Decl) : Array Name :=
  let (name, type, value) := (decl.name, decl.type, decl.value)
  value.getUsedConstants ++ type.getUsedConstants ++ #[name]

end Compiler.LCNF

def RBMap.toArray (self : RBMap α β cmp) : Array (α × β) :=
  self.fold (fun r a b => r.push (a, b)) #[]

end Lean