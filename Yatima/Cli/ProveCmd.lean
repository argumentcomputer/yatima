import Yatima.Cli.Utils

open Cli.Parsed in
def proveRun (p : Cli.Parsed) : IO UInt32 := do
  let mut cronos ← Cronos.new.clock "Compilation"
  match ← cliCompile p with
  | .error err => IO.eprintln err; return 1
  | .ok (compileState, cronos') =>
    cronos ← cronos.clock "Compilation"
    if p.hasFlag "summary" then
      IO.println s!"{compileState.summary}"
      IO.println s!"\n{cronos'.summary}"

    match ← cliTranspile compileState p with
    | .error msg => IO.eprintln msg; return 1
    | .ok _ =>
      let output := p.getD "output" "output"
      let prove := s!"cargo run --release -- prove --expression ../lean_output.lurk --proof {output}.json --lurk"
      match ← runCmd prove with
      | .ok res => IO.println res; return 0
      | .error err => IO.eprintln err; return 1

def proveCmd : Cli.Cmd := `[Cli|
  prove VIA proveRun;
  "Generate a Lurk proof from a Lean declaration"

  FLAGS:
    p, "prelude"; "Optimizes the compilation of prelude files without imports." ++
      " All files to be compiled must follow this rule"
    l, "log";                  "Logs compilation progress"
    s, "summary";              "Prints a compilation summary at the end of the process"
    d, "declaration" : String; "Sets the root call for the Lurk evaluation (defaults to \"root\")"
    o, "output" : String;      "Specifies the target file name for the Lurk code"
    "no-erase-types";          "Do not erase types from the Yatima source"
]
