namespace Yatima

inductive Name
  | anon
  | str : String → Name
  deriving Inhabited, BEq, Ord

def Name.ofLeanName : Lean.Name → Name
  | Lean.Name.anonymous  => .anon
  | s@(Lean.Name.str ..) => .str s.toString
  | _                    => unreachable!

end Yatima
