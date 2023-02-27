prelude
set_option linter.all false -- prevent error messages from runFrontend
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
  inductive BLO'' | blea : BLE'' → BLA' → BLO''
  inductive BLI'' | ble : BLE'' → BLI''
end

-- testing external reference into mutual
inductive BLEH
  | bleh : BLE → BLEH
  | bloh : BLO → BLEH
