import Megaparsec

inductive Noun where
| atom : Nat → Noun
| cell : Noun → Noun → Noun

deriving instance BEq for Noun

def Noun.toString_aux : Noun → String
  | .atom n => toString n
  | .cell m n => 
    String.join ["[", Noun.toString_aux m, " ", Noun.toString_aux n, "]"]

instance : ToString Noun where
  toString := Noun.toString_aux

#eval Noun.cell (Noun.atom 1) (Noun.atom 1)

inductive Expr where 
| noun : Noun → Expr 
| wut : Noun → Expr 
| lus : Noun → Expr 
| tis : Noun → Expr 
| net : Noun → Expr 
| hax : Noun → Expr 
| tar : Noun → Expr 

def Expr.toString_aux : Expr → String
  | .noun n => toString n
  | .wut n => String.join ["?", toString n]
  | .lus n => String.join ["+", toString n]
  | .tis n => String.join ["=", toString n]
  | .net n => String.join ["/", toString n]
  | .hax n => String.join ["#", toString n]
  | .tar n => String.join ["*", toString n]

instance : ToString Expr where
  toString := Expr.toString_aux

#eval Expr.wut (Noun.atom 1)

def wut : Noun → Except Noun Noun
| .cell _ _ => pure (.atom 0)
| .atom _  =>  pure (.atom 1)

def lus : Noun → Except Noun Noun
| .atom n  =>  pure (.atom (n + 1))
| n => Except.error n

def tis : Noun → Except Noun Noun
| .cell m n => if m == n then pure (.atom 0) else pure (.atom 1)
| n => Except.error n

partial def net : Noun → Except Noun Noun
| .cell (.atom 1) a => pure a
| .cell (.atom 2) (.cell a _) => pure a
| .cell (.atom 3) (.cell _ b) => pure b
| .cell (.atom a) b => 
  if a % 2 == 0 then do
    let inner ← net (.cell (.atom (a / 2)) b)
    net (.cell (.atom 2) inner)
  else do
    let inner ← net (.cell (.atom ((a - 1) / 2)) b)
    net (.cell (.atom 3) inner)
| n => Except.error n

partial def hax : Noun → Except Noun Noun
| .cell (.atom 1) (.cell a _) => pure a
| .cell (.atom a) (.cell b c) => 
  if a % 2 == 0 then do
    let e := a / 2
    let inner ← net (.cell (.atom (e + e + 1)) c)
    hax (.cell (.atom e) (.cell (.cell b inner) c))
  else do
    let o := (a - 1) / 2
    let inner ← net (.cell (.atom (o + o)) c)
    hax (.cell (.atom o) (.cell (.cell inner b) c))
| n => Except.error n

partial def tar : Noun -> Except Noun Noun
| .cell a (.cell (.cell b c) d) => do
    let inner0 <- tar (.cell a (.cell b c))
    let inner1 <- tar (.cell a d)
    return (.cell inner0 inner1)
|  .cell a (.cell (.atom 0) b) => net (.cell b a)
|  .cell _ (.cell (.atom 1) b) => return b
|  .cell a (.cell (.atom 2) (.cell b c)) => do
    let inner0 <- tar (.cell a b)
    let inner1 <- tar (.cell a c)
    tar (.cell inner0 inner1)
|  .cell a (.cell (.atom 3) b) => do
    let tard <- tar (.cell a b)
    wut tard
|  .cell a (.cell (.atom 4) b) => do
    let tard <- tar (.cell a b)
    lus tard
|  .cell a (.cell (.atom 5) (.cell b c)) => do
    let tard0 <- tar (.cell a b)
    let tard1 <- tar (.cell a c)
    tis (.cell tard0 tard1)
|  .cell a (.cell (.atom 6) (.cell b (.cell c d))) => do
    let tard0 <- tar (.cell a (.cell (.atom 4) (.cell (.atom 4) b)))
    let tard1 <- tar (.cell (.cell (.atom 2) (.atom 3)) (.cell (.atom 0) tard0))
    let tard2 <- tar (.cell (.cell c d) (.cell (.atom 0) tard1))
    tar (.cell a tard2)
|  .cell a (.cell (.atom 7) (.cell b c)) => do
    let tard <- tar (.cell a b)
    tar (.cell tard c)
|  .cell a (.cell (.atom 8) (.cell b c)) => do
    let tard <- tar (.cell a b)
    tar (.cell (.cell tard a) c)
|  .cell a (.cell (.atom 9) (.cell b c)) => do
    let tard <- tar (.cell a c)
    tar (.cell tard
      (.cell (.atom 2) (.cell (.cell (.atom 0) (.atom 1)) (.cell (.atom 0) b))))
|  .cell a (.cell (.atom 10) (.cell (.cell b c) d)) => do
    let tard0 <- tar (.cell a c)
    let tard1 <- tar (.cell a d)
    hax (.cell b (.cell tard0 tard1))
|  .cell a (.cell (.atom 11) (.cell (.cell _ c) d)) => do
    let tard0 <- tar (.cell a c)
    let tard1 <- tar (.cell a d)
    tar (.cell (.cell tard0 tard1) (.cell (.atom 0) (.atom 3)))
|  .cell a (.cell (.atom 11) (.cell _ c)) =>
    tar (.cell a c)
| n => Except.error n

def nock : Noun -> Except Noun Noun := tar

def eval : Expr -> Except Noun Noun
| .noun n => return n
| .wut  e    => wut e
| .lus  e    => lus e
| .tis  e    => tis e
| .net  e    => net e
| .hax  e    => hax e
| .tar  e    => tar e

open Megaparsec Parsec Common

abbrev P := Parsec Char String Unit

def atomP : P Noun := do
  let x : List Char ← some' (satisfy Char.isDigit)
  let str : String := String.mk x
  return .atom $ String.toNat! str

def blanksP : P Unit := do
  discard $ many' (satisfy fun c => [' ', '\n', '\t'].contains c)

def toCell : Noun → List Noun → Noun
| n, [] => n
| n, x::xs => .cell n (toCell x xs)

mutual 
  partial def cellP : P Noun := do
    discard $ single '['
    let a : Noun ← nounP
    let xs : List Noun ← some' nounP
    discard $ single ']'
    return toCell a xs

  partial def nounP : P Noun := do
    blanksP
    atomP <|> cellP

end

def parseNoun (input : String) : Except String Noun :=
   Except.mapError toString $ parse nounP input

def evalNoun (input : String) : Except String Noun := do
  let n <- parseNoun input
  Except.mapError toString $ nock n

-- #eval evalNoun "[[[4 5] [6 14 15]] [0 7]]"

-- #eval evalNoun "[42 [6 [1 0] [4 0 1] [1 233]]]"

def increment42 := evalNoun "[42 [6 [1 0] [4 0 1] [1 233]]]"
def decrement42 : Except String Noun :=
  evalNoun "[42 [8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]]"