import Yatima.Datatypes.Expr

open Yatima

def root : TC.Expr := .lam default `x .default (.sort default .zero) (.var default `x 0)
