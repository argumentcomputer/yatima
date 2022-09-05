import Lean.Data.Parsec

/-!
## TODO:
Write this in Megaparsec instead
-/

open Lean Parsec

-- TODO : Add more whitespaces (make sure this is right)
def wsChar : List Char := 
  ['\u0009', -- tab
   '\u000a', -- newline
   '\u000d', -- ???
   '\u0020'  -- space
  ]

def bannedChar : List Char := 
  [
    '-',
    '(',
    ')',
    '"',
    '.'
  ]

def isWS := wsChar.elem

def isBanned := bannedChar.elem

def takeWhile (f : Char → Bool) : Parsec String := 
  (many $ satisfy f) >>= 
  fun cs => pure ⟨cs.toList⟩

def pSym : Parsec String := do
  let c ← satisfy $ not ∘ fun c => (decide $ '0' ≤ c ∧ c ≤ '9'  -- symbols can't start with a digit
                                    || isBanned c               -- or with banned chars
                                    || isWS c)                  -- or whitespace
  let s ← takeWhile $ fun c => !isWS c && !isBanned c
  return s!"{c}" ++ s

def pNat : Parsec Nat := 
  many1 digit >>=
  fun cs => return mkNat $ cs.toList.map (·.toNat - 48)
  where mkNat := List.foldl (fun n m => 10 * n + m) 0

def pInt : Parsec Int := 
  (skipChar '-' *> return .negOfNat $ ← pNat) <|> Functor.map .ofNat pNat

def pOneOfString (ws : List String) : Parsec String := 
  ws.firstM fun w => attempt $ pstring w >>=
  fun w => pure w

def pcharButNot (bad : List Char) : Parsec Char := do
  let c ← anyChar
  if bad.elem c then
    fail s!"bad character {c}" else
    return c

open ParseResult in 
def pend : Parsec Unit := fun it => success it ()

def sepBy1 (p : Parsec α) (sep : Char) : Parsec $ Array α :=
  p >>= fun x => many (skipChar sep *> p) >>= fun xs => pure $ xs.reverse.push x |>.reverse

def sepBy (p : Parsec α) (sep : Char) : Parsec $ Array α := sepBy1 p sep <|> pure #[]

def sepByWS1 (p : Parsec α) : Parsec $ Array α := p >>= fun x => many (ws *> p) >>= fun xs =>
  pure $ xs.reverse.push x |>.reverse

def sepByWS (p : Parsec α) : Parsec $ Array α := sepByWS1 p <|> pure #[]