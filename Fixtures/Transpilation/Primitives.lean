def natAdd := 100 + 200
def natSub1 := 100 - 2
def natSub2 := 100 - 200
def natMul := 32 * 32
def natDiv1 := 2 / 3
def natDiv2 := 100 / 3
def natMod1 := 37 % 2
def natMod2 := 37 % 0
def natLe := decide (3 <= 10)
def natBEq := 5 == 4
def natEq := decide (3 == 1000)

def char := 'a'
def charOfNat := Char.ofNat 97 
def charToNat := Char.toNat 'a'

def list := [1, 2, 3, 4, 5, 6]
def listMap := list.map fun x => x + 1
def listFoldl := list.foldl (init := 0) fun acc x => acc + x
def listBeq := list == [1, 2, 3, 4, 5, 6]
def listEq := decide (list = [0, 1, 2])

def abcd := "abcd"
def efg := "efg"
def stringAppend := abcd ++ efg 
def stringLength := stringAppend.length
def stringBeq := abcd == efg
def stringEq := decide (abcd = efg)
