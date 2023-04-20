import YatimaStdLib.Cronos

-- Move to YatimaStdLib
def Cronos.clock! (c : Cronos) (tag : String) : IO Cronos := do
  let now ← IO.monoNanosNow
  match c.refs.find? tag with
  | none => return { c with refs := c.refs.insert tag now }
  | some ref =>
    let time := now - ref
    IO.println s!"  {tag} | {(Float.ofNat time) / 1000000000}s"
    return {
      refs := c.refs.insert tag now,
      data := c.data.insert tag time }
