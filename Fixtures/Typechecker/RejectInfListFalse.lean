partial def inf (u : Unit) : List Unit := u :: inf u

theorem aa : False :=
  nomatch (⟨inf._unsafe_rec (), rfl⟩ : ∃ l, l = () :: l)
