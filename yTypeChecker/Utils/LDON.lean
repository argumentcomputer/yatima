prelude
import yTypeChecker.Utils.Batteries.RBMap
import yTypeChecker.Utils.YSL.Field

namespace Lurk

/--
Reserved symbols are expected to be in uppercase. Planned to be dropped in favor
of LDON.
-/
inductive LDON
  | num : F → LDON
  | u64 : UInt64 → LDON
  | char : Char → LDON
  | str : String → LDON
  | sym : String → LDON
  | cons : LDON → LDON → LDON
  deriving Ord, BEq, Repr, Inhabited

namespace LDON

@[match_pattern] def nil : LDON := sym "NIL"
@[match_pattern] def t   : LDON := sym "T"

def telescopeCons (acc : Array LDON := #[]) : LDON → Array LDON × LDON
  | cons x y => telescopeCons (acc.push x) y
  | x => (acc, x)

def consWith (xs : List LDON) (init : LDON) : LDON :=
  xs.foldr (init := init) cons

def reservedSyms : Batteries.RBSet String compare := .ofList [
  "NIL",
  "T",
  "CURRENT-ENV",
  "BEGIN",
  "IF",
  "LAMBDA",
  "LET",
  "LETREC",
  "QUOTE",
  "ATOM",
  "CAR",
  "CDR",
  "EMIT",
  "EVAL",
  "COMMIT",
  "COMM",
  "OPEN",
  "NUM",
  "CHAR",
  "CONS",
  "STRCONS",
  "+" ,
  "-" ,
  "*" ,
  "/" ,
  "=" ,
  "<" ,
  ">" ,
  "<=" ,
  ">=" ,
  "EQ",
  "HIDE",
  "_",
  "TERMINAL",
  "DUMMY",
  "OUTERMOST",
  "ERROR"
] _

open Std Format in
partial def toFormat (esc : Bool) : LDON → Format
  | num n => format n
  | u64 n => format n
  | char c => s!"#\\{c}"
  | str s => s!"\"{s}\""
  | sym s => if esc && !reservedSyms.contains s then s!"|{s}|" else s
  | x@(.cons ..) =>
    match x.telescopeCons with
    | (xs, nil) => paren $ fmtList xs.data
    | (xs, y) => paren $ fmtList xs.data ++ line ++ "." ++ line ++ (y.toFormat esc)
where
  fmtList : List LDON → Format
    | [] => .nil
    | x::xs => xs.foldl (fun acc x => acc ++ line ++ (x.toFormat esc)) (x.toFormat esc)

def toString (esc : Bool) : LDON → String :=
  ToString.toString ∘ toFormat esc

instance : Std.ToFormat LDON := ⟨toFormat false⟩
instance : ToString LDON := ⟨toString false⟩

namespace Macro

scoped syntax "~[" withoutPosition(term,*) "]"  : term

macro_rules
  | `(~[$xs,*]) => do
    let ret ← xs.getElems.foldrM (fun x xs => `(LDON.cons $x $xs)) (← `(LDON.nil))
    return ret

end Macro

open Macro in
/-- This helper is needed for the DSL and for the parser -/
def mkQuote (x : LDON) : LDON :=
  ~[sym "QUOTE", x]

class ToLDON (α : Type _) where
  toLDON : α → LDON

export ToLDON (toLDON)

instance : ToLDON Nat where
  toLDON := .num ∘ .ofNat

instance : ToLDON Char where
  toLDON := .char

instance : ToLDON String where
  toLDON := .str

instance [ToLDON α] : ToLDON (List α) where
  toLDON es := LDON.consWith (es.map toLDON) .nil

instance [ToLDON α] : ToLDON (Array α) where
  toLDON es := LDON.consWith (es.data.map toLDON) .nil

instance : ToLDON LDON := ⟨id⟩

end Lurk.LDON
