def natAdd := 100 + 200
def natSub1 := 100 - 2
def natSub2 := 100 - 200
def natMul := 32 * 32
def natDiv1 := 2 / 3
def natDiv2 := 100 / 3
def natMod1 := 37 % 2
def natMod2 := 37 % 0
def natLe := decide (3 <= 10)
def natBEqF := 5 == 4
def natBEqT := 5 == 5
def natEqF := decide (3 == 1000)
def natEqT := decide (3 == 3)
def natMatch : Nat → Nat
  | 0 => 0
  | _ + 1 => 10
def natMatchApp := natMatch 2
def natMatchRec : Nat → Nat
  | 0 => 0
  | n + 1 => natMatchRec n + 2 
def natMatchRecApp := natMatchRec 10

def fin10 : (Fin 10) := 5
def finAdd1 : (Fin 10) := 1 + 1
def finAdd2 : (Fin 10) := 7 + 8

def charA := 'a'
def charOfNat := Char.ofNat 97 
def charToNat := Char.toNat 'a'

def list : List Nat := [1, 2, 3, 4, 5, 6]
def listMap := list.map fun x => x + 1
def listFoldl := list.foldl (init := 0) fun acc x => acc + x
def listBeq := list == [1, 2, 3, 4, 5, 6]
def listEqF := decide (list = [0, 1, 2])
def listEqT := decide (list = [1, 2, 3, 4, 5, 6])

def abcd := "abcd"
def efg := "efg"
def stringAppendInst := abcd ++ efg 
def stringAppend := String.append abcd efg 
def stringLength := abcd.length
def stringAppendLength := stringAppend.length
def stringBEqF := abcd == efg
def stringBEqT := abcd == abcd
def stringEqF := decide (abcd = efg)
def stringEqT := decide (abcd = abcd)

def name : Lean.Name := `hello
def nameAppend : Lean.Name := `hello ++ `world
def nameToString := nameAppend.toString