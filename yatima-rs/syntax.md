# Yatima Syntax, a Core syntax for Lean

binders
```
default: (x : A)
implicit {x : A}
strict_implicit {{x : A}}
inst_implicit [x : A]
```

Universes
```
0 ... 1
params: x, y, z
u + n
max u v
imax uv
```

Expressions:
```
Sort u
`foo:bafyqwoieruwqoieruuoqweqwerqw.bafyqwoieruwqoieruuoqweqwerq {u v w}`
x
Π (x : A) -> B
λ (x : A) -> B
let x := t in s
```

Constants:
```
axiom
theorem
opaque
def foo |u v w| (A: Sort u) : Sort u := bar
```

Inductive

```
inductive Foo (x: A) : Sort u
| Bar (x : A) (y : B) : Foo x
| Baz (x : A) (y : B) : Foo y
```

