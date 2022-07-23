import YatimaStdLib.RBMap

structure Cronos where
  refs : Std.RBMap String Float compare
  data : Std.RBMap String Float compare
  deriving Inhabited

namespace Cronos

def new : Cronos :=
  default

private def now : IO Float :=
  return Float.ofNat (← IO.monoMsNow)

variable (c : Cronos)

def start (tag : String) : IO Cronos :=
  return { c with refs := c.refs.insert tag (← now) }

def clock (tag : String) : IO Cronos := do
  let now ← now
  match c.refs.find? tag with
  | some ref =>
    return ⟨c.refs.insert tag now, c.data.insert tag ((now - ref) / 1000.0)⟩
  | none => return ⟨c.refs.insert tag now, c.data.insert tag 0.0⟩

def summary : String :=
  let timings := c.data.fold (init := "")
    fun acc tag time => s!"{acc}\n  {tag} | {time}s"
  s!"Timings:{timings}"

end Cronos
