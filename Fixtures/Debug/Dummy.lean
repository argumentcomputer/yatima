partial def inf (u : Unit) : List Unit := u :: inf u

example : False := nomatch (⟨inf._unsafe_rec (), rfl⟩ : ∃ l, l = () :: l)