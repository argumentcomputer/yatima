import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides

def StringInductiveData : InductiveData :=
  ⟨``String, 0, 0, .ofList [(``String.mk, 1)]⟩

def StringCore : Override.Decl := ⟨``String, ⟦
  ,("String" 0 0)
⟧⟩

def String.mk : Override.Decl := ⟨``String.mk, ⟦
  (lambda (data) (str_mk data))
⟧⟩

def StringMkCases (discr : AST) (alts : Array Override.Alt) : Except String AST := do
  let #[.alt 0 params k] := alts |
    throw "we assume that structures only have one alternative, and never produce `default` match cases"
  let #[data] := params |
    throw s!"`String.mk` case expects exactly 1 param, got\n {params}"
  return ⟦(let (($data (String.data $discr))) $k)⟧

protected def String : Override := Override.ind
  ⟨StringInductiveData, StringCore, #[String.mk], StringMkCases⟩

def String.data : Override := Override.decl ⟨``String.data, ⟦
  (lambda (self) (str_data self))
⟧⟩

def String.utf8ByteSize.go : Override := Override.decl ⟨``String.utf8ByteSize.go, ⟦
  (lambda (cs)
    (if cs
        (+ (String.utf8ByteSize.go (cdr cs)) (String.csize (car cs)))
        0))
⟧⟩

def String.utf8ByteSize : Override := Override.decl ⟨``String.utf8ByteSize, ⟦
  (lambda (s) (String.utf8ByteSize.go (String.data s)))
⟧⟩

def String.length : Override := Override.decl ⟨``String.length, ⟦
  (lambda (s)
    (if (eq s "")
        0
        (+ 1 (String.length (cdr s)))))
⟧⟩

def String.push : Override := Override.decl ⟨``String.push, ⟦
  (lambda (s c) (str_push s c))
⟧⟩

def String.append : Override := Override.decl ⟨``String.append, ⟦
  (lambda (s₁ s₂) (str_append s₁ s₂))
⟧⟩

/-- Note: `String.utf8GetAux` is a private Lean declaration so 
  overriding this might cause some weird name clashes later. -/
def String.utf8GetAux : Override := Override.decl ⟨`String.utf8GetAux, ⟦
  (lambda (cs i p)
    (if cs
        (if (= i p)
            (car cs)
            (String.utf8GetAux (cdr cs) (+ i (String.csize (car cs))) p))
        65))
⟧⟩

def String.get : Override := Override.decl ⟨``String.get, ⟦
  (lambda (s p) (String.utf8GetAux (String.data s) 0 p))
⟧⟩

/-- Note: `String.utf8GetAux?` is a private Lean declaration so 
  overriding this might cause some weird name clashes later. -/
def String.utf8GetAux? : Override := Override.decl ⟨`String.utf8GetAux?, ⟦
  (lambda (cs i p)
    (if cs
        (if (= i p)
            (Option.some (car cs))
            (String.utf8GetAux? (cdr cs) (+ i (String.csize c)) p))
        Option.none))
⟧⟩

def String.get? : Override := Override.decl ⟨``String.get?, ⟦
  (lambda (s p) (String.utf8GetAux? (String.data s) 0 p))
⟧⟩

/-- Note: `String.utf8GetAux!` is a private Lean declaration so 
  overriding this might cause some weird name clashes later. -/
def String.utf8GetAux! : Override := Override.decl ⟨`String.utf8GetAux!, ⟦
  (lambda (cs i p)
    (if cs
        (if (= i p)
            (car cs)
            (String.utf8GetAux! (cdr cs) (+ i (String.csize c)) p))
        ("panic! at `String.utf8GetAux!`")))
⟧⟩

def String.get! : Override := Override.decl ⟨``String.get!, ⟦
  (lambda (s p) (String.utf8GetAux! (String.data s) 0 p))
⟧⟩

/-- Note: `String.utf8SetAux` is a private Lean declaration so 
  overriding this might cause some weird name clashes later. -/
def String.utf8SetAux : Override := Override.decl ⟨`String.utf8GetAux!, ⟦
  (lambda (c cs i p)
    (if cs
        (if (= i p)
            (cons c (car cs))
            (cons (car cs) (String.utf8SetAux c (cdr cs) (+ i (String.csize c)) p)))
        (List.nil "lcErased")))
⟧⟩

def String.set : Override := Override.decl ⟨``String.set, ⟦
  (lambda (s i c) (String.mk (String.utf8SetAux c (String.data s) 0 i)))
⟧⟩

def String.next : Override := Override.decl ⟨``String.next, ⟦
  (lambda (s p) (+ p (String.csize (String.get s p))))
⟧⟩

def String.utf8PrevAux : Override := Override.decl ⟨`String.utf8PrevAux, ⟦
  (lambda (cs i p) 
    (if cs
        (let ((i' (+ i (String.csize (car cs)))))
            (if (= i' p)
                i
                (String.utf8PrevAux (cdr cs) i' p)))
        0))
⟧⟩

def String.prev : Override := Override.decl ⟨``String.prev, ⟦
  (lambda (s p) 
    (if (= p 0)
        0
        (String.utf8PrevAux (String.data s) 0 p)))
⟧⟩

def String.atEnd : Override := Override.decl ⟨``String.atEnd, ⟦
  (lambda (s p) (Nat.decLe (String.utf8ByteSize s) p))
⟧⟩

def String.get' : Override := Override.decl ⟨``String.get', ⟦
  (lambda (s p h) (utf8GetAux (String.data s) 0 p))
⟧⟩

def String.next' : Override := Override.decl ⟨``String.next', ⟦
  (lambda (s p h) (p + (String.csize (String.get s p))))
⟧⟩

def String.extract.go₁ : Override := Override.decl ⟨``String.extract.go₁, ⟦
  (lambda (s i b e)
    (if s
      (if (= i b)
          (String.extract.go₂ s i e)
          (let ((c (car s))
                (cs (cdr s)))
              (String.extract.go₁ cs (+ i (String.csize c)) b e)))
      (List.nil "lcErased")))
⟧⟩

def String.extract.go₂ : Override := Override.decl ⟨``String.extract.go₂, ⟦
  (lambda (s i e)
    (if s
        (if (= i e)
            (List.nil "lcErased")
            (let ((c (car s))
                  (cs (cdr s)))
                (cons c (String.extract.go₂ cs (+ i (String.csize c)) e))))
        (List.nil "lcErased")))
⟧⟩

def String.extract : Override := Override.decl ⟨``String.extract, ⟦
  (lambda (s b e)
    (if (>= b e)
        ""
        (String.mk (String.extract.go₁ (String.data s) 0 b e))))
⟧⟩

def String.hash : Override := Override.decl ⟨``String.hash, ⟦
  (lambda (s) (num (commit s))) -- TODO this is hackish, but if it works hey it works
⟧⟩

def String.decEq : Override := Override.decl ⟨``String.decEq, ⟦
  (lambda (s₁ s₂) (to_bool (eq s₁ s₂)))
⟧⟩

def String.decLt : Override := Override.decl ⟨``String.decLt, ⟦
  (lambda (s₁ s₂)
    (List.hasDecidableLt "lcErased" Nat.decLt Nat.decLt (String.data s₁) (String.data s₂)))
⟧⟩

set_option pp.all true
#print _root_.String.decLt

def String.module := [
  Lurk.Overrides.String,
  String.data,
  String.utf8ByteSize,
  String.utf8ByteSize,
  String.length,
  String.push,
  String.append,
  String.utf8GetAux,
  String.get,
  String.utf8GetAux?,
  String.get?,
  String.utf8GetAux!,
  String.get!,
  String.utf8SetAux,
  String.set,
  String.next,
  String.utf8PrevAux,
  String.prev,
  String.atEnd,
  String.get',
  String.next',
  String.extract,
  String.extract,
  String.extract,
  String.hash,
  String.decEq,
  String.decLt
]

end Overrides

end Lurk