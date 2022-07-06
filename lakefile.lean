import Lake

open Lake DSL

package Yatima {
  supportInterpreter := true
  binName := "yatima"
  dependencies := #[{
    name := `Ipld
    src := Source.git "https://github.com/yatima-inc/Ipld.lean.git" "9d2f32738cffb83e96a07845824cb489a1dcf081"
  },
  {
    name := `Cli
    src := Source.git "https://github.com/mhuisi/lean4-cli.git" "v1.0.0-lnightly-2022-05-21"
  }]
}
