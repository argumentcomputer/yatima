import Yatima.CodeGen.Override

namespace Lurk.Overrides

open Lurk Expr.DSL LDON.DSL DSL
open Yatima.CodeGen

/-! # Some notes on `Char`

In the Lean runtime, `Char` is just `UInt32`. This "representation flattening"
occurs during the `simp` pass of the compiler, and generates `LCNF` declarations
that eliminates the use of `Char`, replacing it with `UInt32`. This means that
all `(c : Char)` arguments are replaced by `(c : UInt32)`. This flattening is
automatic and cannot be disabled by us, so we just have to roll along with it
and treat `Char` as `UInt32` as well. In particular, that means that the code
generated from
```
def charA := 'a'
```
is not `#\a`, as you would expect, but instead `97`, which is the unicode for
`'a'`.

Keep this in mind as you look through the below overrides and write overrides
yourself -- everywhere, we must assume that our `char` input is actually a `u32`

-/

def CharInductiveData : InductiveData :=
  ⟨``Char, 0, 0, .ofList [(``Char.mk, 0)]⟩

def CharCore : Override.Decl := ⟨``Char, ⟦
  ,("Char" 0 0)
⟧⟩

def Char.mk : Override.Decl := ⟨``Char.mk, ⟦
  (lambda (val valid)
    (char (getelem! (getelem! val 2) 3)))
⟧⟩

def CharMkCases (discr : Expr) (alts : Array Override.Alt) : Except String Expr := do
  let #[.alt 0 params k] := alts |
    throw s!"CharMkCases assumes structures having only one alternative, and never produce `default` match, got\n {alts}"
  let #[val, valid] := params |
    throw s!"`Char.mk` case expects exactly 2 param, got\n {params}"
  let val := val.toString false
  let valid := valid.toString false
  return .mkLet [(val, discr), (valid, .atom .t)] k

/-- Note: read the note on `Char` in the file where this is defined. -/
protected def Char : Override := Override.ind
  ⟨CharInductiveData, CharCore, #[Char.mk], CharMkCases⟩

def Char.val : Override := Override.decl ⟨``Char.val, ⟦
  (lambda (self)
    (UInt32.mk (Fin.mk UInt32.size (num self) t)))
⟧⟩

def Char.valid : Override := Override.decl ⟨``Char.valid, ⟦
  (lambda (self) t)
⟧⟩

/--
Convert a `Nat` into a `Char`.
If the `Nat` does not encode a valid unicode scalar value, `'\0'` is returned instead.
-/
def Char.ofNat : Override := .decl ⟨``Char.ofNat, ⟦
  (lambda (n)
    -- TODO: We contradict ourselves and use `or` and `and` here,
    -- because the cost of strict behavior is minimal
    (if (lor (land (<= 0 n) (< n 0xd800)) (land (< 0xdfff n) (< n 0x110000)))
        n
        0))
⟧⟩

def Char.module := [
  Lurk.Overrides.Char,
  Char.val,
  Char.valid,
  Char.ofNat
]

end Lurk.Overrides
