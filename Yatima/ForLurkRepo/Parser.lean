import Yatima.ForLurkRepo.ParserUtil
import Yatima.ForLurkRepo.AST

section Parser 

open Lean Parsec

namespace Lurk.Parser

def parseAtom : Parsec SExpr := do
  let name ← pSym
  return .atom name

def parseNum : Parsec SExpr := do
  let num ← pInt
  return .num num

def parseStr : Parsec SExpr := do
  skipChar '"'
  let x ← many $ pcharButNot ['\"']
  skipChar '"'
  return .str ⟨x.toList⟩

def parseChar : Parsec SExpr := do
  skipChar '#'
  skipChar '\u005c' -- backslash
  return .char $ ← pcharButNot (bannedChar ++ wsChar)

mutual 

partial def parseCons : Parsec SExpr := do
  skipChar '('
  ws
  let car ← parseSExpr
  ws *> skipChar '.' *> ws 
  let cdr ← parseSExpr
  ws
  skipChar ')'
  return .cons car cdr

partial def parseList : Parsec SExpr := do
  skipChar '('
  ws
  let exprs ← sepByWS parseSExpr
  ws
  skipChar ')'
  return .list exprs.data

partial def parseSExpr : Parsec SExpr := 
  parseAtom <|> parseNum <|> parseStr <|> parseChar <|> attempt parseList <|> attempt parseCons
    <|> fail "something went wrong"

end

def parseLisp : String → Except String SExpr := parseSExpr.run

end Lurk.Parser

end Parser

section Translation

namespace SExpr

open Lurk

inductive translationError 
  | numOutOfBound

def toLurk : SExpr → Except translationError Expr
  | .num n => 
    let nat := n.toNat % N -- Work mod `Lurk.N`
    have h : nat < N := by {apply Nat.mod_lt; simp}
    .ok $ .lit $ .num ⟨nat, h⟩
  | .str s => .ok $ .lit $ .str s
  | .char c => .ok $ .lit $ .char c
  | .list es => sorry
  | .cons car cdr => sorry
  | .atom name => sorry

#check Int.ofNat

end SExpr

end Translation