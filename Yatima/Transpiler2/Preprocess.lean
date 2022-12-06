import Lean

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

partial def visitAll (cs : Array Name) : VisitM Unit := do
  for c in cs do visit c

end VisitM

partial def visitAll (constants : ConstMap) (cs : Array Name) : NameSet :=
  let (_, res) := (VisitM.visitAll cs).run constants |>.run .empty
  res

end Lean