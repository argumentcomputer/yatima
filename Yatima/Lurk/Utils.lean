import Lurk.Syntax.DSL
import Yatima.Datatypes.Lean
import Std.Data.RBMap

namespace Lurk.Syntax.AST

open Yatima

open Lurk.Syntax.DSL

mutual

partial def replaceBindersFreeVars (map : Std.RBMap Name AST compare)
    (bindings : List (Name × AST)) (rec : Bool) : List (Name × AST) :=
  sorry

partial def replaceFreeVars (map : Std.RBMap Name AST compare) : AST → AST :=
  sorry

end

instance : ToAST AST where
  toAST a := a

def mkIfElses (ifThens : List (AST × AST)) (finalElse : AST) : AST :=
  match ifThens with
  | [] => .nil
  | [(cond, body)] => ⟦(if $cond $body $finalElse)⟧
  | (cond, body) :: es => ⟦(if $cond $body $(mkIfElses es finalElse))⟧

def mkMutualBlock (mutuals : List (Name × AST)) : List (Name × AST) :=
  match mutuals with
  | [_] => mutuals
  | _ =>
    let names := mutuals.map Prod.fst
    let mutualName := names.foldl (init := `__mutual__) fun acc n => acc ++ n
    let fnProjs := names.enum.map fun (i, (n : Name)) => (n, ⟦($mutualName $i)⟧)
    let map := fnProjs.foldl (init := default) fun acc (n, e) => acc.insert n e
    let mutualBlock := mkIfElses (mutuals.enum.map fun (i, _, e) =>
        (⟦(= mutidx $i)⟧, replaceFreeVars map e)
      ) ⟦nil⟧
    (mutualName, ⟦(lambda (mutidx) $mutualBlock)⟧) :: fnProjs

end Lurk.Syntax.AST
