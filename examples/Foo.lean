prelude

-- inductive BLA
--   | nil
--   | bla : BLA → BLA → BLA

mutual
inductive BLE | bli : BLI → BLE
inductive BLI | ble : BLE → BLI
end
