def array := #[1, 2, 3, 4, 5, 6]
def arrayGet1 := array.get ⟨0, by simp⟩
def arrayGet2 := array[0]
def arrayGet!1 := array.get! 0
def arrayGet!2 := array[1]!
def arrayGet!Out := array[10]!
def arraySet := array.set ⟨5, by simp⟩ 0
def arrayGet5 := arraySet[5]
def arraySet! := array.set! 0 0
def arrayGet!5 := arraySet![0]!

def arrayFoldl := Id.run do array.foldlM (init := 0) fun acc n => return acc + n