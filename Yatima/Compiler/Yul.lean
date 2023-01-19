-- This is based on Yul's specification https://docs.soliditylang.org/en/v0.8.17/yul.html#specification-of-yul
namespace Yul

-- Yul currently only supports the u256 type, but other types might be added in the future
inductive PrimType where
| u256

abbrev Identifier := String
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

abbrev Code := String
def Code.inc (code : Code) : Code := "    " ++ code

def PrimType.toCode : PrimType → Code
| .u256 => "u256"

def Identifier.toCode (id : Identifier) : Code := id

def TypedIdentifier.toCode (id : TypedIdentifier) : Code :=
  match id.type with
  | none => id.identifier
  | some type => id.identifier ++ " : " ++ type.toCode

mutual

-- Should not be partial functions, but Lean fails to prove termination
partial def Block.toCode (alreadyIndented : Bool) (indent : Code) : Block → Code
| .mk statements =>
  let firstIndent := if alreadyIndented then "" else indent
  let left := firstIndent ++ "{\n"
  let inner := statements.foldr
    (fun statement acc => Statement.toCode indent.inc statement ++ "\n" ++ acc)
    ""
  let right := indent ++ "}"
  left ++ inner ++ right

partial def Statement.toCode (indent : Code) : Statement → Code
| .block block => block.toCode false indent
| .functionDefinition  name args rets body =>
  let header := indent ++ "function " ++ name.toCode
  let args := match args with
    | .nil => "()"
    | .cons arg args' =>
      args'.foldr
        (fun arg' acc => ", " ++ TypedIdentifier.toCode arg' ++ acc)
        ("(" ++ arg.toCode)
      ++ ")"
  let rets := match rets with
    | .nil => ""
    | .cons ret rets' =>
      rets'.foldr
        (fun ret' acc => ", " ++ TypedIdentifier.toCode ret' ++ acc)
        ("-> " ++ ret.toCode)
  let body := body.toCode true indent.inc
  header ++ args ++ rets ++ body
| .variableDeclaration names expr =>
  let firstVar := indent ++ "let " ++ names.head.toCode
  let otherVars := names.tail.foldr (fun name acc => ", " ++ name.toCode ++ acc) ""
  match expr with
  | none => firstVar ++ otherVars
  | some expr => firstVar ++ otherVars ++ " := " ++ expr.toCode true indent.inc
| .assignment          names expr =>
  let firstVar := indent ++ names.head.toCode
  let otherVars := names.tail.foldr (fun name acc => ", " ++ name.toCode ++ acc) ""
  firstVar ++ otherVars ++ " := " ++ expr.toCode true indent.inc
| .«if»                expr block =>
  let indent' := indent.inc
  let ifPart := indent ++ "if " ++ expr.toCode true indent'
  let inner  := block.toCode true indent'
  ifPart ++ inner
| .expression          expr => expr.toCode false indent
| .switch              switch => switch.toCode indent
| .forLoop             init expr inc body =>
  let indent' := indent.inc
  let forPart := indent ++ "for " ++
    init.toCode true indent' ++
    expr.toCode true indent' ++
    inc.toCode true indent'
  let inner := body.toCode true indent'
  forPart ++ inner
| .«break»             => indent ++ "break"
| .«continue»          => indent ++ "continue"
| .leave               => indent ++ "leave"

partial def Expression.toCode (alreadyIndented : Bool) (indent : Code) : Expression → Code := default

partial def Switch.toCode (indent : Code) : Switch → Code := default

end

end Yul
