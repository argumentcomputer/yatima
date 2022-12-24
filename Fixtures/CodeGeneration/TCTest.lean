import Yatima.Typechecker.Typechecker
import Std.Data.RBMap

open Yatima Typechecker TC

def store : Store :=
{ consts := #[Yatima.TC.Const.definition
                { name := `Empty.casesOn,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `Empty 22 [])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `Empty 22 [])
                              (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 1) (Yatima.TC.Expr.var `t 0))),
                  value := Yatima.TC.Expr.lam
                             `motive
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.pi
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `Empty 22 [])
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                             (Yatima.TC.Expr.lam
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `Empty 22 [])
                               (Yatima.TC.Expr.app
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.const `Empty.rec 32 [Yatima.TC.Univ.var `u 0])
                                   (Yatima.TC.Expr.var `motive 1))
                                 (Yatima.TC.Expr.var `t 0))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [0] },
              Yatima.TC.Const.intRecursor
                { name := `True.rec,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `True 4 [])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                            (Yatima.TC.Expr.pi
                              `intro
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.app
                                (Yatima.TC.Expr.var `motive 0)
                                (Yatima.TC.Expr.const `True.intro 12 []))
                              (Yatima.TC.Expr.pi
                                `t
                                (Lean.BinderInfo.default)
                                (Yatima.TC.Expr.const `True 4 [])
                                (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 2) (Yatima.TC.Expr.var `t 0)))),
                  params := 0,
                  indices := 0,
                  motives := 1,
                  minors := 1,
                  k := true,
                  ind := 4 },
              Yatima.TC.Const.axiom
                { name := `lcUnreachable,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `α
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                            (Yatima.TC.Expr.var `α 0),
                  safe := false },
              Yatima.TC.Const.definition
                { name := `Not,
                  lvls := [],
                  type := Yatima.TC.Expr.pi
                            `a
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.zero))
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.zero)),
                  value := Yatima.TC.Expr.lam
                             `a
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.sort (Yatima.TC.Univ.zero))
                             (Yatima.TC.Expr.pi
                               (Lean.Name.mkNum `a.«_@»._hyg 139)
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.var `a 0)
                               (Yatima.TC.Expr.const `False 16 [])),
                  safety := Lean.DefinitionSafety.safe,
                  all := [3] },
              Yatima.TC.Const.inductive
                { name := `True,
                  lvls := [],
                  type := Yatima.TC.Expr.sort (Yatima.TC.Univ.zero),
                  params := 0,
                  indices := 0,
                  recr := false,
                  safe := true,
                  refl := false,
                  unit := true,
                  struct := some { 
                              name := `True.intro,
                              lvls := [],
                              type := Yatima.TC.Expr.const `True 4 [],
                              idx := 0,
                              params := 0,
                              fields := 0,
                              rhs := Yatima.TC.Expr.lam
                                       `motive
                                       (Lean.BinderInfo.default)
                                       (Yatima.TC.Expr.pi
                                         `t
                                         (Lean.BinderInfo.default)
                                         (Yatima.TC.Expr.const `True 4 [])
                                         (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                                       (Yatima.TC.Expr.lam
                                         `intro
                                         (Lean.BinderInfo.default)
                                         (Yatima.TC.Expr.app
                                           (Yatima.TC.Expr.var `motive 0)
                                           (Yatima.TC.Expr.const `True.intro 12 []))
                                         (Yatima.TC.Expr.var `intro 0)),
                              safe := true,
                              all := [4, 12, 1] } },
              Yatima.TC.Const.definition
                { name := `False.recOn,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `False 16 [])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `False 16 [])
                              (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 1) (Yatima.TC.Expr.var `t 0))),
                  value := Yatima.TC.Expr.lam
                             `motive
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.pi
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `False 16 [])
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                             (Yatima.TC.Expr.lam
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `False 16 [])
                               (Yatima.TC.Expr.app
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.const `False.rec 10 [Yatima.TC.Univ.var `u 0])
                                   (Yatima.TC.Expr.var `motive 1))
                                 (Yatima.TC.Expr.var `t 0))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [5] },
              Yatima.TC.Const.definition
                { name := `PEmpty.casesOn,
                  lvls := [`u_1, `u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PEmpty 25 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PEmpty 25 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 1) (Yatima.TC.Expr.var `t 0))),
                  value := Yatima.TC.Expr.lam
                             `motive
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.pi
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `PEmpty 25 [Yatima.TC.Univ.var `u 1])
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                             (Yatima.TC.Expr.lam
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `PEmpty 25 [Yatima.TC.Univ.var `u 1])
                               (Yatima.TC.Expr.app
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.const
                                     `PEmpty.rec
                                     35
                                     [Yatima.TC.Univ.var `u_1 0, Yatima.TC.Univ.var `u 1])
                                   (Yatima.TC.Expr.var `motive 1))
                                 (Yatima.TC.Expr.var `t 0))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [6] },
              Yatima.TC.Const.intRecursor
                { name := `PUnit.rec,
                  lvls := [`u_1, `u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                            (Yatima.TC.Expr.pi
                              `unit
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.app
                                (Yatima.TC.Expr.var `motive 0)
                                (Yatima.TC.Expr.const `PUnit.unit 15 [Yatima.TC.Univ.var `u 1]))
                              (Yatima.TC.Expr.pi
                                `t
                                (Lean.BinderInfo.default)
                                (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                                (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 2) (Yatima.TC.Expr.var `t 0)))),
                  params := 0,
                  indices := 0,
                  motives := 1,
                  minors := 1,
                  k := false,
                  ind := 19 },
              Yatima.TC.Const.definition
                { name := `id,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `α
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                            (Yatima.TC.Expr.pi
                              `a
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.var `α 0)
                              (Yatima.TC.Expr.var `α 1)),
                  value := Yatima.TC.Expr.lam
                             `α
                             (Lean.BinderInfo.implicit)
                             (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                             (Yatima.TC.Expr.lam
                               `a
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.var `α 0)
                               (Yatima.TC.Expr.var `a 0)),
                  safety := Lean.DefinitionSafety.safe,
                  all := [8] },
              Yatima.TC.Const.definition
                { name := `Unit,
                  lvls := [],
                  type := Yatima.TC.Expr.sort (Yatima.TC.Univ.succ (Yatima.TC.Univ.zero)),
                  value := Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.succ (Yatima.TC.Univ.zero)],
                  safety := Lean.DefinitionSafety.safe,
                  all := [9] },
              Yatima.TC.Const.intRecursor
                { name := `False.rec,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `False 16 [])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `False 16 [])
                              (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 1) (Yatima.TC.Expr.var `t 0))),
                  params := 0,
                  indices := 0,
                  motives := 1,
                  minors := 0,
                  k := false,
                  ind := 16 },
              Yatima.TC.Const.definition
                { name := `inferInstance,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `α
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                            (Yatima.TC.Expr.pi
                              `i
                              (Lean.BinderInfo.instImplicit)
                              (Yatima.TC.Expr.var `α 0)
                              (Yatima.TC.Expr.var `α 1)),
                  value := Yatima.TC.Expr.lam
                             `α
                             (Lean.BinderInfo.implicit)
                             (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                             (Yatima.TC.Expr.lam
                               `i
                               (Lean.BinderInfo.instImplicit)
                               (Yatima.TC.Expr.var `α 0)
                               (Yatima.TC.Expr.var `i 0)),
                  safety := Lean.DefinitionSafety.safe,
                  all := [11] },
              Yatima.TC.Const.constructor
                { name := `True.intro,
                  lvls := [],
                  type := Yatima.TC.Expr.const `True 4 [],
                  idx := 0,
                  params := 0,
                  fields := 0,
                  rhs := Yatima.TC.Expr.lam
                           `motive
                           (Lean.BinderInfo.default)
                           (Yatima.TC.Expr.pi
                             `t
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.const `True 4 [])
                             (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                           (Yatima.TC.Expr.lam
                             `intro
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.app
                               (Yatima.TC.Expr.var `motive 0)
                               (Yatima.TC.Expr.const `True.intro 12 []))
                             (Yatima.TC.Expr.var `intro 0)),
                  safe := true,
                  all := [4, 12, 1] },
              Yatima.TC.Const.definition
                { name := `absurd,
                  lvls := [`v],
                  type := Yatima.TC.Expr.pi
                            `a
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.zero))
                            (Yatima.TC.Expr.pi
                              `b
                              (Lean.BinderInfo.implicit)
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `v 0))
                              (Yatima.TC.Expr.pi
                                `h₁
                                (Lean.BinderInfo.default)
                                (Yatima.TC.Expr.var `a 1)
                                (Yatima.TC.Expr.pi
                                  `h₂
                                  (Lean.BinderInfo.default)
                                  (Yatima.TC.Expr.app (Yatima.TC.Expr.const `Not 3 []) (Yatima.TC.Expr.var `a 2))
                                  (Yatima.TC.Expr.var `b 2)))),
                  value := Yatima.TC.Expr.lam
                             `a
                             (Lean.BinderInfo.implicit)
                             (Yatima.TC.Expr.sort (Yatima.TC.Univ.zero))
                             (Yatima.TC.Expr.lam
                               `b
                               (Lean.BinderInfo.implicit)
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `v 0))
                               (Yatima.TC.Expr.lam
                                 `h₁
                                 (Lean.BinderInfo.default)
                                 (Yatima.TC.Expr.var `a 1)
                                 (Yatima.TC.Expr.lam
                                   `h₂
                                   (Lean.BinderInfo.default)
                                   (Yatima.TC.Expr.app (Yatima.TC.Expr.const `Not 3 []) (Yatima.TC.Expr.var `a 2))
                                   (Yatima.TC.Expr.app
                                     (Yatima.TC.Expr.app
                                       (Yatima.TC.Expr.const `False.rec 10 [Yatima.TC.Univ.var `v 0])
                                       (Yatima.TC.Expr.lam
                                         (Lean.Name.mkNum `x.«_@»._hyg 164)
                                         (Lean.BinderInfo.default)
                                         (Yatima.TC.Expr.const `False 16 [])
                                         (Yatima.TC.Expr.var `b 3)))
                                     (Yatima.TC.Expr.app (Yatima.TC.Expr.var `h₂ 0) (Yatima.TC.Expr.var `h₁ 1)))))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [13] },
              Yatima.TC.Const.axiom
                { name := `lcProof,
                  lvls := [],
                  type := Yatima.TC.Expr.pi
                            `α
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.zero))
                            (Yatima.TC.Expr.var `α 0),
                  safe := false },
              Yatima.TC.Const.constructor
                { name := `PUnit.unit,
                  lvls := [`u],
                  type := Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 0],
                  idx := 0,
                  params := 0,
                  fields := 0,
                  rhs := Yatima.TC.Expr.lam
                           `motive
                           (Lean.BinderInfo.default)
                           (Yatima.TC.Expr.pi
                             `t
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                             (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                           (Yatima.TC.Expr.lam
                             `unit
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.app
                               (Yatima.TC.Expr.var `motive 0)
                               (Yatima.TC.Expr.const `PUnit.unit 15 [Yatima.TC.Univ.var `u 1]))
                             (Yatima.TC.Expr.var `unit 0)),
                  safe := true,
                  all := [19, 15, 7] },
              Yatima.TC.Const.inductive
                { name := `False,
                  lvls := [],
                  type := Yatima.TC.Expr.sort (Yatima.TC.Univ.zero),
                  params := 0,
                  indices := 0,
                  recr := false,
                  safe := true,
                  refl := false,
                  unit := false,
                  struct := none },
              Yatima.TC.Const.definition
                { name := `PUnit.casesOn,
                  lvls := [`u_1, `u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.pi
                                `unit
                                (Lean.BinderInfo.default)
                                (Yatima.TC.Expr.app
                                  (Yatima.TC.Expr.var `motive 1)
                                  (Yatima.TC.Expr.const `PUnit.unit 15 [Yatima.TC.Univ.var `u 1]))
                                (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 2) (Yatima.TC.Expr.var `t 1)))),
                  value := Yatima.TC.Expr.lam
                             `motive
                             (Lean.BinderInfo.implicit)
                             (Yatima.TC.Expr.pi
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                             (Yatima.TC.Expr.lam
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                               (Yatima.TC.Expr.lam
                                 `unit
                                 (Lean.BinderInfo.default)
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.var `motive 1)
                                   (Yatima.TC.Expr.const `PUnit.unit 15 [Yatima.TC.Univ.var `u 1]))
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.app
                                     (Yatima.TC.Expr.app
                                       (Yatima.TC.Expr.const
                                         `PUnit.rec
                                         7
                                         [Yatima.TC.Univ.var `u_1 0, Yatima.TC.Univ.var `u 1])
                                       (Yatima.TC.Expr.var `motive 2))
                                     (Yatima.TC.Expr.var `unit 0))
                                   (Yatima.TC.Expr.var `t 1)))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [17] },
              Yatima.TC.Const.definition
                { name := `Function.const,
                  lvls := [`u, `v],
                  type := Yatima.TC.Expr.pi
                            `α
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                            (Yatima.TC.Expr.pi
                              `β
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `v 1))
                              (Yatima.TC.Expr.pi
                                `a
                                (Lean.BinderInfo.default)
                                (Yatima.TC.Expr.var `α 1)
                                (Yatima.TC.Expr.pi
                                  (Lean.Name.mkNum `a.«_@»._hyg 54)
                                  (Lean.BinderInfo.default)
                                  (Yatima.TC.Expr.var `β 1)
                                  (Yatima.TC.Expr.var `α 3)))),
                  value := Yatima.TC.Expr.lam
                             `α
                             (Lean.BinderInfo.implicit)
                             (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                             (Yatima.TC.Expr.lam
                               `β
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `v 1))
                               (Yatima.TC.Expr.lam
                                 `a
                                 (Lean.BinderInfo.default)
                                 (Yatima.TC.Expr.var `α 1)
                                 (Yatima.TC.Expr.lam
                                   (Lean.Name.mkNum `x.«_@»._hyg 59)
                                   (Lean.BinderInfo.default)
                                   (Yatima.TC.Expr.var `β 1)
                                   (Yatima.TC.Expr.var `a 1)))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [18] },
              Yatima.TC.Const.inductive
                { name := `PUnit,
                  lvls := [`u],
                  type := Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0),
                  params := 0,
                  indices := 0,
                  recr := false,
                  safe := true,
                  refl := false,
                  unit := true,
                  struct := some { 
                              name := `PUnit.unit,
                              lvls := [`u],
                              type := Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 0],
                              idx := 0,
                              params := 0,
                              fields := 0,
                              rhs := Yatima.TC.Expr.lam
                                       `motive
                                       (Lean.BinderInfo.default)
                                       (Yatima.TC.Expr.pi
                                         `t
                                         (Lean.BinderInfo.default)
                                         (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                                         (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                                       (Yatima.TC.Expr.lam
                                         `unit
                                         (Lean.BinderInfo.default)
                                         (Yatima.TC.Expr.app
                                           (Yatima.TC.Expr.var `motive 0)
                                           (Yatima.TC.Expr.const `PUnit.unit 15 [Yatima.TC.Univ.var `u 1]))
                                         (Yatima.TC.Expr.var `unit 0)),
                              safe := true,
                              all := [19, 15, 7] } },
              Yatima.TC.Const.definition
                { name := `True.casesOn,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `True 4 [])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `True 4 [])
                              (Yatima.TC.Expr.pi
                                `intro
                                (Lean.BinderInfo.default)
                                (Yatima.TC.Expr.app
                                  (Yatima.TC.Expr.var `motive 1)
                                  (Yatima.TC.Expr.const `True.intro 12 []))
                                (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 2) (Yatima.TC.Expr.var `t 1)))),
                  value := Yatima.TC.Expr.lam
                             `motive
                             (Lean.BinderInfo.implicit)
                             (Yatima.TC.Expr.pi
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `True 4 [])
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                             (Yatima.TC.Expr.lam
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `True 4 [])
                               (Yatima.TC.Expr.lam
                                 `intro
                                 (Lean.BinderInfo.default)
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.var `motive 1)
                                   (Yatima.TC.Expr.const `True.intro 12 []))
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.app
                                     (Yatima.TC.Expr.app
                                       (Yatima.TC.Expr.const `True.rec 1 [Yatima.TC.Univ.var `u 0])
                                       (Yatima.TC.Expr.var `motive 2))
                                     (Yatima.TC.Expr.var `intro 0))
                                   (Yatima.TC.Expr.var `t 1)))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [20] },
              Yatima.TC.Const.definition
                { name := `PEmpty.recOn,
                  lvls := [`u_1, `u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PEmpty 25 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PEmpty 25 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 1) (Yatima.TC.Expr.var `t 0))),
                  value := Yatima.TC.Expr.lam
                             `motive
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.pi
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `PEmpty 25 [Yatima.TC.Univ.var `u 1])
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                             (Yatima.TC.Expr.lam
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `PEmpty 25 [Yatima.TC.Univ.var `u 1])
                               (Yatima.TC.Expr.app
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.const
                                     `PEmpty.rec
                                     35
                                     [Yatima.TC.Univ.var `u_1 0, Yatima.TC.Univ.var `u 1])
                                   (Yatima.TC.Expr.var `motive 1))
                                 (Yatima.TC.Expr.var `t 0))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [21] },
              Yatima.TC.Const.inductive
                { name := `Empty,
                  lvls := [],
                  type := Yatima.TC.Expr.sort (Yatima.TC.Univ.succ (Yatima.TC.Univ.zero)),
                  params := 0,
                  indices := 0,
                  recr := false,
                  safe := true,
                  refl := false,
                  unit := false,
                  struct := none },
              Yatima.TC.Const.axiom
                { name := `lcCast,
                  lvls := [`u, `v],
                  type := Yatima.TC.Expr.pi
                            `α
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                            (Yatima.TC.Expr.pi
                              `β
                              (Lean.BinderInfo.implicit)
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `v 1))
                              (Yatima.TC.Expr.pi
                                `a
                                (Lean.BinderInfo.default)
                                (Yatima.TC.Expr.var `α 1)
                                (Yatima.TC.Expr.var `β 1))),
                  safe := false },
              Yatima.TC.Const.definition
                { name := `PUnit.recOn,
                  lvls := [`u_1, `u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.pi
                                `unit
                                (Lean.BinderInfo.default)
                                (Yatima.TC.Expr.app
                                  (Yatima.TC.Expr.var `motive 1)
                                  (Yatima.TC.Expr.const `PUnit.unit 15 [Yatima.TC.Univ.var `u 1]))
                                (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 2) (Yatima.TC.Expr.var `t 1)))),
                  value := Yatima.TC.Expr.lam
                             `motive
                             (Lean.BinderInfo.implicit)
                             (Yatima.TC.Expr.pi
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                             (Yatima.TC.Expr.lam
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `PUnit 19 [Yatima.TC.Univ.var `u 1])
                               (Yatima.TC.Expr.lam
                                 `unit
                                 (Lean.BinderInfo.default)
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.var `motive 1)
                                   (Yatima.TC.Expr.const `PUnit.unit 15 [Yatima.TC.Univ.var `u 1]))
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.app
                                     (Yatima.TC.Expr.app
                                       (Yatima.TC.Expr.const
                                         `PUnit.rec
                                         7
                                         [Yatima.TC.Univ.var `u_1 0, Yatima.TC.Univ.var `u 1])
                                       (Yatima.TC.Expr.var `motive 2))
                                     (Yatima.TC.Expr.var `unit 0))
                                   (Yatima.TC.Expr.var `t 1)))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [24] },
              Yatima.TC.Const.inductive
                { name := `PEmpty,
                  lvls := [`u],
                  type := Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0),
                  params := 0,
                  indices := 0,
                  recr := false,
                  safe := true,
                  refl := false,
                  unit := false,
                  struct := none },
              Yatima.TC.Const.definition
                { name := `Empty.recOn,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `Empty 22 [])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `Empty 22 [])
                              (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 1) (Yatima.TC.Expr.var `t 0))),
                  value := Yatima.TC.Expr.lam
                             `motive
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.pi
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `Empty 22 [])
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                             (Yatima.TC.Expr.lam
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `Empty 22 [])
                               (Yatima.TC.Expr.app
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.const `Empty.rec 32 [Yatima.TC.Univ.var `u 0])
                                   (Yatima.TC.Expr.var `motive 1))
                                 (Yatima.TC.Expr.var `t 0))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [26] },
              Yatima.TC.Const.definition
                { name := `Unit.unit,
                  lvls := [],
                  type := Yatima.TC.Expr.const `Unit 9 [],
                  value := Yatima.TC.Expr.const `PUnit.unit 15 [Yatima.TC.Univ.succ (Yatima.TC.Univ.zero)],
                  safety := Lean.DefinitionSafety.safe,
                  all := [27] },
              Yatima.TC.Const.definition
                { name := `inferInstanceAs,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `α
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                            (Yatima.TC.Expr.pi
                              `i
                              (Lean.BinderInfo.instImplicit)
                              (Yatima.TC.Expr.var `α 0)
                              (Yatima.TC.Expr.var `α 1)),
                  value := Yatima.TC.Expr.lam
                             `α
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                             (Yatima.TC.Expr.lam
                               `i
                               (Lean.BinderInfo.instImplicit)
                               (Yatima.TC.Expr.var `α 0)
                               (Yatima.TC.Expr.var `i 0)),
                  safety := Lean.DefinitionSafety.safe,
                  all := [28] },
              Yatima.TC.Const.definition
                { name := `Function.comp,
                  lvls := [`u, `v, `w],
                  type := Yatima.TC.Expr.pi
                            `α
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                            (Yatima.TC.Expr.pi
                              `β
                              (Lean.BinderInfo.implicit)
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `v 1))
                              (Yatima.TC.Expr.pi
                                `δ
                                (Lean.BinderInfo.implicit)
                                (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `w 2))
                                (Yatima.TC.Expr.pi
                                  `f
                                  (Lean.BinderInfo.default)
                                  (Yatima.TC.Expr.pi
                                    (Lean.Name.mkNum `a.«_@»._hyg 19)
                                    (Lean.BinderInfo.default)
                                    (Yatima.TC.Expr.var `β 1)
                                    (Yatima.TC.Expr.var `δ 1))
                                  (Yatima.TC.Expr.pi
                                    `g
                                    (Lean.BinderInfo.default)
                                    (Yatima.TC.Expr.pi
                                      (Lean.Name.mkNum `a.«_@»._hyg 22)
                                      (Lean.BinderInfo.default)
                                      (Yatima.TC.Expr.var `α 3)
                                      (Yatima.TC.Expr.var `β 3))
                                    (Yatima.TC.Expr.pi
                                      (Lean.Name.mkNum `a.«_@»._hyg 25)
                                      (Lean.BinderInfo.default)
                                      (Yatima.TC.Expr.var `α 4)
                                      (Yatima.TC.Expr.var `δ 3)))))),
                  value := Yatima.TC.Expr.lam
                             `α
                             (Lean.BinderInfo.implicit)
                             (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                             (Yatima.TC.Expr.lam
                               `β
                               (Lean.BinderInfo.implicit)
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `v 1))
                               (Yatima.TC.Expr.lam
                                 `δ
                                 (Lean.BinderInfo.implicit)
                                 (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `w 2))
                                 (Yatima.TC.Expr.lam
                                   `f
                                   (Lean.BinderInfo.default)
                                   (Yatima.TC.Expr.pi
                                     (Lean.Name.mkNum `a.«_@»._hyg 19)
                                     (Lean.BinderInfo.default)
                                     (Yatima.TC.Expr.var `β 1)
                                     (Yatima.TC.Expr.var `δ 1))
                                   (Yatima.TC.Expr.lam
                                     `g
                                     (Lean.BinderInfo.default)
                                     (Yatima.TC.Expr.pi
                                       (Lean.Name.mkNum `a.«_@»._hyg 22)
                                       (Lean.BinderInfo.default)
                                       (Yatima.TC.Expr.var `α 3)
                                       (Yatima.TC.Expr.var `β 3))
                                     (Yatima.TC.Expr.lam
                                       `x
                                       (Lean.BinderInfo.default)
                                       (Yatima.TC.Expr.var `α 4)
                                       (Yatima.TC.Expr.app
                                         (Yatima.TC.Expr.var `f 2)
                                         (Yatima.TC.Expr.app (Yatima.TC.Expr.var `g 1) (Yatima.TC.Expr.var `x 0)))))))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [29] },
              Yatima.TC.Const.axiom
                { name := `lcErased,
                  lvls := [],
                  type := Yatima.TC.Expr.sort (Yatima.TC.Univ.succ (Yatima.TC.Univ.zero)),
                  safe := false },
              Yatima.TC.Const.definition
                { name := `False.casesOn,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `False 16 [])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `False 16 [])
                              (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 1) (Yatima.TC.Expr.var `t 0))),
                  value := Yatima.TC.Expr.lam
                             `motive
                             (Lean.BinderInfo.default)
                             (Yatima.TC.Expr.pi
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `False 16 [])
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                             (Yatima.TC.Expr.lam
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `False 16 [])
                               (Yatima.TC.Expr.app
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.const `False.rec 10 [Yatima.TC.Univ.var `u 0])
                                   (Yatima.TC.Expr.var `motive 1))
                                 (Yatima.TC.Expr.var `t 0))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [31] },
              Yatima.TC.Const.intRecursor
                { name := `Empty.rec,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `Empty 22 [])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `Empty 22 [])
                              (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 1) (Yatima.TC.Expr.var `t 0))),
                  params := 0,
                  indices := 0,
                  motives := 1,
                  minors := 0,
                  k := false,
                  ind := 22 },
              Yatima.TC.Const.definition
                { name := `False.elim,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `C
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                            (Yatima.TC.Expr.pi
                              `h
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `False 16 [])
                              (Yatima.TC.Expr.var `C 1)),
                  value := Yatima.TC.Expr.lam
                             `C
                             (Lean.BinderInfo.implicit)
                             (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0))
                             (Yatima.TC.Expr.lam
                               `h
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `False 16 [])
                               (Yatima.TC.Expr.app
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.const `False.rec 10 [Yatima.TC.Univ.var `u 0])
                                   (Yatima.TC.Expr.lam
                                     (Lean.Name.mkNum `x.«_@»._hyg 150)
                                     (Lean.BinderInfo.default)
                                     (Yatima.TC.Expr.const `False 16 [])
                                     (Yatima.TC.Expr.var `C 2)))
                                 (Yatima.TC.Expr.var `h 0))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [33] },
              Yatima.TC.Const.definition
                { name := `True.recOn,
                  lvls := [`u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.implicit)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `True 4 [])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `True 4 [])
                              (Yatima.TC.Expr.pi
                                `intro
                                (Lean.BinderInfo.default)
                                (Yatima.TC.Expr.app
                                  (Yatima.TC.Expr.var `motive 1)
                                  (Yatima.TC.Expr.const `True.intro 12 []))
                                (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 2) (Yatima.TC.Expr.var `t 1)))),
                  value := Yatima.TC.Expr.lam
                             `motive
                             (Lean.BinderInfo.implicit)
                             (Yatima.TC.Expr.pi
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `True 4 [])
                               (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u 0)))
                             (Yatima.TC.Expr.lam
                               `t
                               (Lean.BinderInfo.default)
                               (Yatima.TC.Expr.const `True 4 [])
                               (Yatima.TC.Expr.lam
                                 `intro
                                 (Lean.BinderInfo.default)
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.var `motive 1)
                                   (Yatima.TC.Expr.const `True.intro 12 []))
                                 (Yatima.TC.Expr.app
                                   (Yatima.TC.Expr.app
                                     (Yatima.TC.Expr.app
                                       (Yatima.TC.Expr.const `True.rec 1 [Yatima.TC.Univ.var `u 0])
                                       (Yatima.TC.Expr.var `motive 2))
                                     (Yatima.TC.Expr.var `intro 0))
                                   (Yatima.TC.Expr.var `t 1)))),
                  safety := Lean.DefinitionSafety.safe,
                  all := [34] },
              Yatima.TC.Const.intRecursor
                { name := `PEmpty.rec,
                  lvls := [`u_1, `u],
                  type := Yatima.TC.Expr.pi
                            `motive
                            (Lean.BinderInfo.default)
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PEmpty 25 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.sort (Yatima.TC.Univ.var `u_1 0)))
                            (Yatima.TC.Expr.pi
                              `t
                              (Lean.BinderInfo.default)
                              (Yatima.TC.Expr.const `PEmpty 25 [Yatima.TC.Univ.var `u 1])
                              (Yatima.TC.Expr.app (Yatima.TC.Expr.var `motive 1) (Yatima.TC.Expr.var `t 0))),
                  params := 0,
                  indices := 0,
                  motives := 1,
                  minors := 0,
                  k := false,
                  ind := 25 }],
  primIdxs := Std.RBMap.ofList [] _,
  idxsToPrims := Std.RBMap.ofList [] _ }

def runCheckStore := TypecheckM.run (.init store) (.init store) typecheckM

#eval runCheckStore