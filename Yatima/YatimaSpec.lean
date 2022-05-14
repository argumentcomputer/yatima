syntax "it " str " so " term " should be " term: doElem
syntax "it " str " so " term " should be empty": doElem
syntax "it " str " so " term " shouldn't be " term: doElem
syntax "it " str " so " term " shouldn't be empty": doElem

syntax (name := testSuite) withPosition("test_suite" colGt doElem*) : command

set_option hygiene false in
macro_rules
  | `(doElem| it $s so $l should be $r) =>
    `(doElem|
      if $l == $r then
        IO.println $ "✓ " ++ $s
      else failures := failures.concat $s)
  | `(doElem| it $s so $l should be empty) =>
    `(doElem|
      if List.isEmpty $l then
        IO.println $ "✓ " ++ $s
      else failures := failures.concat $s)
  | `(doElem| it $s so $l shouldn't be $r) =>
    `(doElem|
      if $l != $r then
        IO.println $ "✓ " ++ $s
      else failures := failures.concat $s)
  | `(doElem| it $s so $l shouldn't be empty) =>
    `(doElem|
      if not List.isEmpty $l then
        IO.println $ "✓ " ++ $s
      else failures := failures.concat $s)
  | `(testSuite| test_suite $ts*) =>
    `(def main : IO UInt32 := do
        let mut failures : List String := []
        $[$ts:doElem]*
        if not failures.isEmpty then do
          IO.eprintln $ "· Failed tests:\n  × " ++ "\n  × ".intercalate failures
          return 1
        else return 0)
