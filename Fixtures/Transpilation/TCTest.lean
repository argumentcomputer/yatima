import Yatima.Typechecker.Typechecker
import Std.Data.RBMap

open Yatima Typechecker TC

def store : Store :=
{ consts := #[Const.definition
                { name := `id,
                  lvls := [`u],
                  type := Expr.pi
                            `α
                            (Lean.BinderInfo.implicit)
                            (Expr.sort (Univ.var `u 0))
                            (Expr.pi
                              `a
                              (Lean.BinderInfo.default)
                              (Expr.var `α 0)
                              (Expr.var `α 1)),
                  value := Expr.lam
                             `α
                             (Lean.BinderInfo.implicit)
                             (Expr.sort (Univ.var `u 0))
                             (Expr.lam
                               `a
                               (Lean.BinderInfo.default)
                               (Expr.var `α 0)
                               (Expr.var `a 0)),
                  safety := Lean.DefinitionSafety.safe,
                  all := [0] },
              Const.definition
                { name := `Function.const,
                  lvls := [`u, `v],
                  type := Expr.pi
                            `α
                            (Lean.BinderInfo.implicit)
                            (Expr.sort (Univ.var `u 0))
                            (Expr.pi
                              `β
                              (Lean.BinderInfo.default)
                              (Expr.sort (Univ.var `v 1))
                              (Expr.pi
                                `a
                                (Lean.BinderInfo.default)
                                (Expr.var `α 1)
                                (Expr.pi
                                  (Lean.Name.mkNum `a.«_@»._hyg 54)
                                  (Lean.BinderInfo.default)
                                  (Expr.var `β 1)
                                  (Expr.var `α 3)))),
                  value := Expr.lam
                             `α
                             (Lean.BinderInfo.implicit)
                             (Expr.sort (Univ.var `u 0))
                             (Expr.lam
                               `β
                               (Lean.BinderInfo.default)
                               (Expr.sort (Univ.var `v 1))
                               (Expr.lam
                                 `a
                                 (Lean.BinderInfo.default)
                                 (Expr.var `α 1)
                                 (Expr.lam
                                   (Lean.Name.mkNum `x.«_@»._hyg 59)
                                   (Lean.BinderInfo.default)
                                   (Expr.var `β 1)
                                   (Expr.var `a 1)))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [1] },
              Const.definition
                { name := `Function.comp,
                  lvls := [`u, `v, `w],
                  type := Expr.pi
                            `α
                            (Lean.BinderInfo.implicit)
                            (Expr.sort (Univ.var `u 0))
                            (Expr.pi
                              `β
                              (Lean.BinderInfo.implicit)
                              (Expr.sort (Univ.var `v 1))
                              (Expr.pi
                                `δ
                                (Lean.BinderInfo.implicit)
                                (Expr.sort (Univ.var `w 2))
                                (Expr.pi
                                  `f
                                  (Lean.BinderInfo.default)
                                  (Expr.pi
                                    (Lean.Name.mkNum `a.«_@»._hyg 19)
                                    (Lean.BinderInfo.default)
                                    (Expr.var `β 1)
                                    (Expr.var `δ 1))
                                  (Expr.pi
                                    `g
                                    (Lean.BinderInfo.default)
                                    (Expr.pi
                                      (Lean.Name.mkNum `a.«_@»._hyg 22)
                                      (Lean.BinderInfo.default)
                                      (Expr.var `α 3)
                                      (Expr.var `β 3))
                                    (Expr.pi
                                      (Lean.Name.mkNum `a.«_@»._hyg 25)
                                      (Lean.BinderInfo.default)
                                      (Expr.var `α 4)
                                      (Expr.var `δ 3)))))),
                  value := Expr.lam
                             `α
                             (Lean.BinderInfo.implicit)
                             (Expr.sort (Univ.var `u 0))
                             (Expr.lam
                               `β
                               (Lean.BinderInfo.implicit)
                               (Expr.sort (Univ.var `v 1))
                               (Expr.lam
                                 `δ
                                 (Lean.BinderInfo.implicit)
                                 (Expr.sort (Univ.var `w 2))
                                 (Expr.lam
                                   `f
                                   (Lean.BinderInfo.default)
                                   (Expr.pi
                                     (Lean.Name.mkNum `a.«_@»._hyg 19)
                                     (Lean.BinderInfo.default)
                                     (Expr.var `β 1)
                                     (Expr.var `δ 1))
                                   (Expr.lam
                                     `g
                                     (Lean.BinderInfo.default)
                                     (Expr.pi
                                       (Lean.Name.mkNum `a.«_@»._hyg 22)
                                       (Lean.BinderInfo.default)
                                       (Expr.var `α 3)
                                       (Expr.var `β 3))
                                     (Expr.lam
                                       `x
                                       (Lean.BinderInfo.default)
                                       (Expr.var `α 4)
                                       (Expr.app
                                         (Expr.var `f 2)
                                         (Expr.app (Expr.var `g 1) (Expr.var `x 0)))))))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [2] }],
  primIdxs := Std.RBMap.ofList [] _,
  idxsToPrims := Std.RBMap.ofList [] _}

def type := store.consts[0].type

def runInfer := TypecheckM.run (.init store) (.init store) (infer type)

deriving instance Repr for TypecheckError
deriving instance Repr for TypedExpr

def test : Except String Unit :=
  match TypecheckM.run (.init store) (.init store) typecheckM with
  | .ok u => .ok u
  | .error err => throw $ toString err