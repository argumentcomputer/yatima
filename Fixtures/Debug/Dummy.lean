import Lean.CoreM

-- #eval Lean.addDecl <| .mutualDefnDecl [{
--   name := `False_intro
--   levelParams := []
--   type := .const ``False []
--   value := .const `False_intro []
--   hints := .opaque
--   safety := .partial
-- }]

-- theorem False.intro : False := False_intro

partial def inf (u : Unit) : List Unit := u :: inf u

theorem aa : False :=
  nomatch (⟨inf._unsafe_rec (), rfl⟩ : ∃ l, l = () :: l)