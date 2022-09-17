import Lean.Data.RBMap

def stuff : Std.RBMap Nat Nat compare := 
  Std.RBMap.ofList [(0, 0), (1, 1), (2, 2)]
def root := stuff.insert 3 3 
