import Yatima.Typechecker.Typechecker
import Std.Data.RBMap

open Yatima Typechecker TC

def run' (ctx : TypecheckCtx) (stt : TypecheckState) (m : TypecheckM α) : Except TypecheckError α :=
  match ExceptT.run $ (StateT.run (ReaderT.run m ctx) stt) with
  | .error e => .error e
  | .ok (a, _) => .ok a

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

instance [Repr α] : Repr (Thunk α) where
  reprPrec tk prec := Repr.addAppParen ("Thunk.pure " ++ reprArg tk.get) prec

deriving instance Repr for Value
deriving instance Repr for SusValue

#eval runInfer

def typedExpr := TypedExpr.pi
 (SusTypeInfo.sort
     (Univ.imax (Univ.succ (Univ.var `u 0)) (Univ.var `u 0)))
  `α
  Lean.BinderInfo.implicit
  (TypedExpr.sort
     (SusTypeInfo.sort (Univ.succ (Univ.var `u 0)))
     (Univ.var `u 0))
  (TypedExpr.pi
     (SusTypeInfo.sort (Univ.var `u 0))
     `a
     Lean.BinderInfo.default
     (TypedExpr.var (SusTypeInfo.sort (Univ.var `u 0)) `α 0)
     (TypedExpr.var (SusTypeInfo.sort (Univ.var `u 0)) `α 1))

def runEval := TypecheckM.run (.init store) (.init store) (eval typedExpr)

#eval runEval

def runSuspend := suspend typedExpr (.init store) (.init store)

#eval runSuspend

def runEqual := TypecheckM.run (.init store) (.init store) (equal 0 runSuspend runSuspend)

#eval runEqual

def runCheckStore := TypecheckM.run (.init store) (.init store) typecheckM

#eval runCheckStore
