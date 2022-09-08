import Yatima.ForLurkRepo.ParserUtil
import Yatima.ForLurkRepo.AST
import YatimaStdLib.List

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

def binaryOps : List (String × BinaryOp) := 
  [
    ("+", .sum),
    ("-", .diff),
    ("*", .prod),
    ("/", .quot),
    ("=", .numEq),
    ("eq", .eq),
    ("<", .lt),
    (">", .gt),
    ("≤", .le),
    ("≥", .ge)
  ]

inductive translationError 
  | numOutOfBound
  | badShape -- Add more errors
  | noNames 
  | noName
  | illFormedBinder
  | badFuncApp

partial def extractName : SExpr → Except translationError Name
  | .atom name => .ok name
  | _ => throw .noName

partial def extractNames : SExpr → Except translationError (List Name)
  | .atom name => .ok [name]
  | .list exprs => exprs.mapM extractName
  | .cons (.atom name1) (.atom name2) => .ok [name1, name2]
  | _ => throw .noNames

partial def extractBinder : SExpr → Except translationError (Name × SExpr)
  | .list exprs => if exprs.length > 2 then throw .illFormedBinder else
    match exprs[0]! with
      | .atom name => .ok (name, exprs[1]!)
      | _ => throw .illFormedBinder
  | _ => throw .illFormedBinder

partial def extractBinders : SExpr → Except translationError (List $ Name × SExpr)
  | .list exprs => exprs.mapM extractBinder
  | _ => throw .illFormedBinder

mutual

partial def mkSpine (head : Name ⊕ Expr) (args : List SExpr) : Except translationError Expr :=
  let rec go (args : List SExpr) (term : Expr) : Except translationError Expr :=
    match args with
      | [] => .ok term
      | arg :: args => return ← go args $ .app term (← toLurk arg)
  match head with
    | .inl name => go args $ .sym name
    | .inr expr => go args expr

partial def toLurk : SExpr → Except translationError Expr
  | .num n => 
    let nat := n.toNat % N -- Work mod `Lurk.N`
    have h : nat < N := by {apply Nat.mod_lt; simp}
    .ok $ .lit $ .num ⟨nat, h⟩
  | .str s => .ok $ .lit $ .str s
  | .char c => .ok $ .lit $ .char c
  | .list es => 
    match es[0]! with
      | .atom "if" => 
        match toLurk es[1]!, toLurk es[2]!, toLurk es[3]! with
           | .ok test, .ok conseq, .ok alt => .ok $ .ifE test conseq alt
           | _, _, _ => throw .badShape -- TODO: improve errors
      | .atom "lambda" =>
        let formals := es[1]!
        match extractNames formals with
          | .ok names => 
            match toLurk es[2]! with
              | .ok body => .ok $ .lam names body
              | _ => throw .badShape -- TODO: improve errors
          | .error ε => throw ε
      | .atom "let" => do
        let sBinders ← extractBinders es[1]!
        let binders ← sBinders.mapM fun (n, sexpr) => return (n, ← toLurk sexpr)
        return .letE binders (← toLurk es[2]!)
      | .atom "letrec" =>  do
        let sBinders ← extractBinders es[1]!
        let binders ← sBinders.mapM fun (n, sexpr) => return (n, ← toLurk sexpr)
        return .letRecE binders (← toLurk es[2]!)
      | .atom "quote" => do
        if es.length == 2 then 
          return .quote es[1]! else
          throw .badShape
      | .atom "cons" => do
        if es.length == 3 then
          let car ← toLurk es[1]!
          let cdr ← toLurk es[2]!
          return .cons car cdr else
          throw .badShape
      | .atom "strcons" => do
        if es.length == 3 then
          let car ← toLurk es[1]!
          let cdr ← toLurk es[2]!
          return .strcons car cdr else
          throw .badShape
      | .atom "atom" => do
        if es.length == 2 then
          return .atom (← toLurk es[1]!) else
          throw .badShape
      | .atom "car" => do
        if es.length == 2 then
          let cons ← toLurk es[1]!
          return .car cons else
          throw .badShape
      | .atom "cdr" => do
        if es.length == 2 then
          let cons ← toLurk es[1]!
          return .cdr cons else
          throw .badShape
      | .atom "emit" => do
        if es.length == 2 then
          return .emit (← toLurk es[1]!) else
          throw .badShape
      | .atom "begin" => do
        return .begin (← es.tail!.mapM toLurk)
      | .atom "current-env" => do
        if es.length == 1 then return .currEnv else throw .badShape
      | .atom head => do
        let idx? := binaryOps.map (fun (a,b) => a) |>.indexOf? head
        match idx? with
          | .some idx => 
            if es.length == 3 then 
            return .binaryOp binaryOps[idx]!.2 (← toLurk es[1]!) (← toLurk es[2]!) else
            throw .badShape
          | .none => if es.length == 1 then 
            return .app₀ $ .sym head else
            return ← mkSpine (.inl head) es.tail!
      | head@(.list _) => do
        let func ← toLurk head
        return ← mkSpine (.inr func) es.tail!
      | .num _
      | .str _
      | .char _ 
      | .cons .. => throw .badFuncApp
  | .cons car cdr => return .cons (← toLurk car) (← toLurk cdr)
  | .atom name => if name == "current-env" then .ok .currEnv else .ok $ .sym name

end

end SExpr

end Translation
