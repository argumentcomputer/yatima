namespace Yatima

inductive Name
  | str : String → Name
  deriving BEq, Ord, Inhabited

def Name.ofLeanName : Lean.Name → Name
  | Lean.Name.anonymous  => .str ""
  | s@(Lean.Name.str ..) => .str s.toString
  | _                    => unreachable!

end Yatima
