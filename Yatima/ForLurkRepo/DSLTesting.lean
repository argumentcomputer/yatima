import Yatima.ForLurkRepo.DSL

namespace Lurk.Tests

def binds := [`foo, `bar]
-- #eval ⟦
--     (lambda ($binds) a)
--  ⟧.pprint

def names := [`a, `b, `c]
def name := `d

-- #eval ⟦
--   (lambda ($names $name e) ())
-- ⟧.pprint

-- #eval ⟦ (quote («t»)) ⟧.pprint
-- (lambda (n)
--   n)

-- #eval IO.println $ ⟦
-- (let (
--     (foo (lambda (a) (a)))
--     (bar (lambda (x) (x))))
--   (foo "1" 2 3))
-- ⟧.pprint.pretty 25
-- (let (
--     (foo
--       (lambda (a)
--         (a)))
--     (bar
--       (lambda (x)
--         (x))))
--   (foo
--     "1"
--     2
--     3))

def foo : Expr := ⟦
(let ((foo (lambda (a b c)
             (* (+ a b) c))))
  (foo "1" 2 3))
⟧

-- #eval IO.print $ ⟦$foo⟧.pprint.pretty 25
-- (let (
--     (foo
--       (lambda (a b c)
--         (*
--           (+
--             a
--             b)
--           c))))
--   (foo
--     "1"
--     2
--     3))

-- #eval IO.print $ ⟦
-- (let ()
--   (foo "1" 2 3))
-- ⟧.pprint.pretty 25
-- (let ()
--   (foo
--     "1"
--     2
--     3))

-- #eval IO.print $ ⟦
-- ("s")
-- ⟧.pprint.pretty 25
-- ("s")

def m : Nat := 1
def n := [[1, 2], []]

-- #eval IO.print $ ⟦
-- (quote ($n $m "s" n))
-- ⟧.pprint.pretty 25
-- (quote (((1 2) ()) 1 "s"))

def test := [SExpr| 
  ($n $m "s")
]

-- #eval IO.print $ ⟦
--   (quote ($test 1))
-- ⟧.pprint.pretty 35
-- (quote ((((1 2) ()) 1 "s") 1))