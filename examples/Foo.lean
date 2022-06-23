inductive Bar
  | hi | bye

def bar := Bar.hi

inductive MyNat
| zero : MyNat
| succ : MyNat → MyNat
