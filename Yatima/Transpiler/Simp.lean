import Lurk.Syntax.AST

/-!
# Simp
A rudimentary simplifier for lurk expressions. 
* Current we only plan to support things like 
  `(OfNat.ofNat Nat n (instOfNatNat n)) => n`
* There is a more principled way to do this, 
  so this file should be taken as a hack and not 
  built upon heavily.
-/
namespace Yatima.Transpiler.Simp

open Lurk.Syntax AST

def simpStep : AST → AST
  | x@~[sym "OfNat.ofNat", sym "Nat", num n, ~[sym "instOfNatNat", num m]] =>
    if n == m then num n else x
  | ~[sym "HAdd.hAdd", .sym "Nat", .sym "Nat", .sym "Nat",
      ~[.sym "instHAdd", .sym "Nat", .sym "instAddNat"], (.num x), (.num y)] =>
    .num (x + y)
  | ~[.sym "HMul.hMul", .sym "Nat", .sym "Nat", .sym "Nat",
      ~[.sym "instHMul", .sym "Nat", .sym "instMulNat"], (.num x), (.num y)] =>
    .num (x * y)
  | ~[.sym "HAppend.hAppend", .sym "String", .sym "String", .sym "String",
      ~[.sym "instHAppend", .sym "String", .sym "String.instAppendString"], x, y]
  | ~[.sym "String.append", x, y] => ~[.sym "str_append", x, y]
  | .cons x y => .cons (simpStep x) (simpStep y)
  | x => x

partial def simp (ast : AST) : AST := Id.run do
  let mut ast  := ast
  let mut ast' := simpStep ast
  while ast' != ast do
    ast := ast'
    ast' := simpStep ast'
  pure ast'

end Yatima.Transpiler.Simp
