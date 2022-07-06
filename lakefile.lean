import Lake

open Lake DSL

package Yatima {
  supportInterpreter := true
  binName := "yatima"
  dependencies := #[{
    name := `Ipld
    src := Source.git "https://github.com/yatima-inc/Ipld.lean.git" "2940e8d8abeda81bd4eda119d12521e477a2490b"
  }, {
    name := `LSpec
    src := Source.git "https://github.com/yatima-inc/LSpec.git" "56da3b774818df05f44d3fc7621a6888b716ee4a"
  }, {
    name := `YatimaStdLib,
    src := Source.git "https://github.com/yatima-inc/YatimaStdLib.lean" "b57d71878e6d9762c75f99b07b4bacdefdadeeaf"
  }, {
    name := `Cli
    src := Source.git "https://github.com/mhuisi/lean4-cli.git" "v1.0.0-lnightly-2022-05-21"
  }]
}
