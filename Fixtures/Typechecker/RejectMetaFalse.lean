import Lean.CoreM

#eval Lean.addDecl <| .mutualDefnDecl [{
  name := `FalseIntro
  levelParams := []
  type := .const ``False []
  value := .const `FalseIntro []
  hints := .opaque
  safety := .partial
}]

theorem False.intro : False := FalseIntro
