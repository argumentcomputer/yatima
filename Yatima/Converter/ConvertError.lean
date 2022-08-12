inductive ConvertError where
  | ipldError : ConvertError
  | cannotStoreValue : ConvertError
  | mutDefBlockFound : ConvertError
  | mutIndBlockFound : ConvertError
  | anonMetaMismatch : String → String → ConvertError
  | cannotFindNameIdx : String → ConvertError
  | constIdxOutOfRange : Nat → Nat → ConvertError
  | invalidIndexDepth : Nat → Nat → ConvertError
  | invalidMutBlock : String → ConvertError
  | unexpectedConst : String → String → ConvertError
  | defnsIdxNotFound : String → ConvertError
  | mutRefFVNotFound : Nat → ConvertError
  deriving Inhabited

instance : ToString ConvertError where toString
  | .anonMetaMismatch anon meta => s!"Anon/Meta mismatch: Anon is of kind {anon} but Meta is of kind {meta}"
  | .ipldError => "IPLD broken"
  | .cannotStoreValue => "Cannot store value"
  | .mutDefBlockFound => "Found a mutual definition block inside an expression"
  | .mutIndBlockFound => "Found a mutual inductive block inside an expression"
  | .cannotFindNameIdx name => s!"Cannot find index for '{name}'"
  | .constIdxOutOfRange i max => s!"Const index {i} out of range. Must be < {max}"
  | .invalidIndexDepth i min => s!"Invalid mutual referencing free variable index {i}. Must be ≥ {min}"
  | .invalidMutBlock type => s!"Invalid mutual block Ipld.Const reference, {type} found."
  | .defnsIdxNotFound name => s!"Could not find {name} in index of definitions."
  | .mutRefFVNotFound i => s!"Could not find index {i} in index of mutual referencing free variables."
  | .unexpectedConst got exp => s!"Unexpected constant. Got {got} but expected {exp}"
