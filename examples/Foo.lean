prelude

def foo {α β γ : Type} : α → (β → γ) → α := fun a f => a

inductive BLA
  | nil
  | bla : BLA → BLA → BLA

inductive BLAH | blah : BLA → BLAH

#print BLAH.rec

-- mutual
--   inductive BLE | bli : BLI → BLE
--   inductive BLI | ble : BLE → BLI
--   inductive BLO | blea : BLE → BLA → BLO
-- end

-- inductive BLEH
--   | bleh : BLE → BLEH
--   | bloh : BLO → BLEH

-- mutual
--   inductive Tree (A : Type) where
--     | branch : (a : A) → (trees : TreeList A) → Tree A

--   inductive TreeList (A : Type) where
--     | nil : TreeList A
--     | cons : (t : Tree A) → (ts : TreeList A) → TreeList A
-- end

-- inductive List (α : Type u) where 
--   | nil : List α
--   | cons (a : α) (as : List α) : List α

-- inductive Treew (A : Type) where
--   | branch : (a : A) → (trees : List (Treew A)) → Treew A

-- mutual
--   inductive Treeq (A : Type) where
--     | branch : TreeListq A → (a : A) → (trees : List (Treeq A)) → Treeq A

--   inductive TreeListq (A : Type) where
--     | nil : TreeListq A
--     | cons : (t : Treeq A) → (ts : TreeListq A) → TreeListq A
-- end

-- #print TreeList.recOn