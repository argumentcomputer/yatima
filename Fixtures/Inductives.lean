prelude

inductive BLA
  | nil
  | bla : BLA → BLA → BLA

-- an inductive with a differently named constructor but all else equal should be the smae
inductive BLU
  | nil
  | blu : BLU → BLU → BLU

-- an inductive with a different constructor order should be distinct
inductive BLA'
  | bla : BLA' → BLA' → BLA'
  | nil

mutual
  -- BLE and BLI should be distinct because we don't group by weak equality
  inductive BLE | bli : BLI → BLE
  inductive BLI | ble : BLE → BLI
  inductive BLO | blea : BLE → BLI → BLO
end

mutual
  inductive BLE' | bli : BLI' → BLE'
  inductive BLI' | ble : BLE' → BLI'
  inductive BLO' | blea : BLE' → BLI' → BLO'
end

mutual
  -- BLE and BLI should be distinct because we don't group by weak equality
  inductive BLE'' | bli : BLI'' → BLE''
  inductive BLO'' | blea : BLE'' → BLA'' → BLO''
  inductive BLI'' | ble : BLE'' → BLI''
end

-- testing external reference into mutual
inductive BLEH
  | bleh : BLE → BLEH
  | bloh : BLO → BLEH

inductive Option (α : Type u) where 
  | none : Option α
  | some (a : α) : Option α

inductive List (α : Type u) where 
  | nil : List α
  | cons (a : α) (as : List α) : List α

-- nested inductive
inductive Treew (A : Type) where
  | branch : (a : A) → (trees : List (Treew A)) → Treew A

-- multiply nested inductive
inductive Treer (A : Type) where
  | branch : (a : A) → (tree? : Option (Treer A)) → (trees : List (Treer A)) → Treer A

mutual
  -- mutual and multiply nested inductive
  inductive Treeq (A : Type) where
    | branch : TreeListq A → (a : A) → (tree? : Option (Treer A)) → (trees : List (Treeq A)) → Treeq A

  inductive TreeListq (A : Type) where
    | nil : TreeListq A
    | cons : (t : Treeq A) → (ts : TreeListq A) → TreeListq A

  inductive TreeListx (A : Type) where
    | nil : TreeListx A
    | cons : (t : Treeq A) → (ts : TreeListx A) → TreeListx A
end
