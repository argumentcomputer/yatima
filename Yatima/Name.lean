namespace Yatima

abbrev Name := String

def Name.ofLeanName : Lean.Name → Name
  | s@(.str ..) => s.toString
  | _           => ""

end Yatima