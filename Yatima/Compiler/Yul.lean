-- This is based on Yul's specification https://docs.soliditylang.org/en/v0.8.17/yul.html#specification-of-yul
namespace Yul

-- Yul currently only supports the u256 type, but other types might be added in the future
inductive PrimType where
| u256

def Identifier := String
structure TypedIdentifier where
  identifier : Identifier
  type       : Option PrimType

inductive Literal where
-- Actually it should be a u256
| number : PrimType → Nat → Literal
| string : PrimType → String → Literal
| true   : PrimType → Literal
| false  : PrimType → Literal

inductive Expression where
| functionCall : Identifier → List Expression → Expression
| identifier   : Identifier → Expression
| literal      : Literal → Expression

structure NonemptyList (α : Type u) where
  head : α
  tail : List α

def NonemptyList.toList (xs : NonemptyList α) : List α := xs.head :: xs.tail

mutual

inductive Block where
| mk : List Statement → Block

inductive Switch where
| case    : Expression → NonemptyList (Literal × Block) → Option Block → Switch
| default : Expression → Block → Switch

inductive Statement where
| block               : Block → Statement
| functionDefinition  : Identifier → List TypedIdentifier → List TypedIdentifier → Block → Statement
| variableDeclaration : NonemptyList TypedIdentifier → Option Expression → Statement
| assignment          : NonemptyList Identifier → Expression → Statement
| «if»                : Expression → Block → Statement
| expression          : Expression → Statement
| switch              : Switch → Statement
| forLoop             : Block → Expression → Block → Block → Statement
| «break»             : Statement
| «continue»          : Statement
| leave               : Statement

end

mutual

-- Should not be partial functions, but Lean fails to prove termination
partial def blockToCode (alreadyIndented : Bool) (indent : String) : Block → String
| .mk statements =>
  let firstIndent := if alreadyIndented then "" else indent
  let left := firstIndent ++ "{\n"
  let inner := statements.foldr
    (fun statement acc => statementToCode ("    " ++ indent) statement ++ "\n" ++ acc)
    ""
  let right := indent ++ "}"
  left ++ inner ++ right

partial def statementToCode (indent : String) : Statement → String
| .block block => blockToCode false indent block
| .functionDefinition  name args rets body => sorry
| .variableDeclaration names expr => sorry
| .assignment          name expr => sorry
| .«if»                expr block =>
  let ifPart := indent ++ "if " ++ expressionToCode true indent expr
  let inner  := blockToCode true indent block
  ifPart ++ inner
| .expression          expr => expressionToCode false indent expr
| .switch              switch => switchToCode indent switch
| .forLoop             init expr inc body =>
  let forPart := indent ++ "for " ++
    blockToCode true indent init ++
    expressionToCode true indent expr ++
    blockToCode true indent inc
  let inner := blockToCode true indent body
  forPart ++ inner
| .«break»             => indent ++ "break"
| .«continue»          => indent ++ "continue"
| .leave               => indent ++ "leave"

partial def expressionToCode (alreadyIndented : Bool) (indent : String) : Expression → String := sorry

partial def switchToCode (indent : String) : Switch → String := sorry

end

end Yul
