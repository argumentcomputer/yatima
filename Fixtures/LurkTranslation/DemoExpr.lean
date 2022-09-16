import Yatima.Datatypes.Expr

def root : Yatima.Expr := 
  .lam default `x default (.sort default Yatima.Univ.zero) (.var default `x 1)
