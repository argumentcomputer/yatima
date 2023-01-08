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

inductive BreakContinue
| «break»
| «continue»

structure NonemptyList (α : Type u) where
  head : α
  tail : List α

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
| breakContinue       : BreakContinue → Statement
| leave               : Statement

end

end Yul
