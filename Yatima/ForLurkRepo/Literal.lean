import Lean

open Lean Elab Meta Term

open Std
namespace Lurk

def N := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- Basic Lurk primitives -/
inductive Literal
  -- `t` `nil`
  | t | nil
  -- Numerical values
  | num  : Fin N → Literal
  -- Strings
  | str  : String → Literal
  -- Characters
  | char : Char → Literal
  deriving Repr, BEq, Inhabited

namespace Literal 

partial def pprintLit (l : Literal) : Format :=
  match l with
  | .nil        => "nil"
  | .t          => "t"
  | .num ⟨n, _⟩ => if n < USize.size then toString n else List.asString (Nat.toDigits 16 n)
  | .str s      => s!"\"{s}\""
  | .char c     => s!"#\\{c}"

instance : ToFormat Literal where
  format := pprintLit

end Literal

def mkNumLit (n : Nat) : Literal :=
  .num (Fin.ofNat n)

def mkNameLit (name : String) := 
  mkAppM ``Name.mkSimple #[mkStrLit name]

declare_syntax_cat    lurk_literal
syntax "t"          : lurk_literal
syntax "nil"        : lurk_literal
-- syntax "-" noWs num : lurk_literal
syntax num          : lurk_literal
syntax str          : lurk_literal
syntax char         : lurk_literal

def elabLiteral : Syntax → TermElabM Expr
  | `(lurk_literal| t)   => return mkConst ``Lurk.Literal.t
  | `(lurk_literal| nil) => return mkConst ``Lurk.Literal.nil
  -- | `(lurk_literal| -$n) => match n.getNat with
  --   | 0     => do
  --     mkAppM ``Lurk.Literal.num #[← mkAppM ``Fin.ofNat #[mkConst ``Nat.zero]]
  --   | n + 1 => do
  --     mkAppM ``Lurk.Literal.num #[← mkAppM ``Fin.ofInt #[← mkAppM ``Int.negSucc #[mkNatLit n]]]
  | `(lurk_literal| $n:num) => do
    mkAppM ``Lurk.mkNumLit #[mkNatLit n.getNat]
  | `(lurk_literal| $s:str) =>
    mkAppM ``Lurk.Literal.str #[mkStrLit s.getString]
  | `(lurk_literal| $c:char) => do
    let c ← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]
    mkAppM ``Lurk.Literal.char #[c]
  | _ => throwUnsupportedSyntax

end Lurk