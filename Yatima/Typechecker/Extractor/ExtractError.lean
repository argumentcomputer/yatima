namespace Yatima.Extractor

/-- Errors that can be thrown in `Yatima.Extractor.ExtractM` -/
inductive ExtractError where
  | irError : ExtractError
  | cannotStoreValue : ExtractError
  | mutDefBlockFound : ExtractError
  | mutIndBlockFound : ExtractError
  | anonMetaMismatch : String → String → ExtractError
  | cannotFindNameIdx : String → ExtractError
  | constIdxOutOfRange : Nat → Nat → ExtractError
  | invalidIndexDepth : Nat → Nat → ExtractError
  | invalidMutBlock : String → ExtractError
  | unexpectedConst : String → String → ExtractError
  | constIdxNotFound : String → ExtractError
  | mutRefFVNotFound : Nat → ExtractError
  deriving Inhabited

instance : ToString ExtractError where toString
  | .anonMetaMismatch anon meta => s!"Anon/Meta mismatch: Anon is of kind {anon} but Meta is of kind {meta}"
  | .irError => "IR broken"
  | .cannotStoreValue => "Cannot store value"
  | .mutDefBlockFound => "Found a mutual definition block inside an expression"
  | .mutIndBlockFound => "Found a mutual inductive block inside an expression"
  | .cannotFindNameIdx name => s!"Cannot find index for '{name}'"
  | .constIdxOutOfRange i max => s!"Const index {i} out of range. Must be < {max}"
  | .invalidIndexDepth i min => s!"Invalid mutual referencing free variable index {i}. Must be ≥ {min}"
  | .invalidMutBlock type => s!"Invalid mutual block Ipld.Const reference, {type} found."
  | .constIdxNotFound name => s!"Could not find {name} in index of definitions."
  | .mutRefFVNotFound i => s!"Could not find index {i} in index of mutual referencing free variables."
  | .unexpectedConst got exp => s!"Unexpected constant. Got {got} but expected {exp}"

end Yatima.Extractor
