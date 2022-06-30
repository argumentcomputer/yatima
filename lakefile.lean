import Lake

open Lake DSL

package Yatima {
  supportInterpreter := true
  binName := "yatima"
  dependencies := #[{
    name := `Ipld
    src := Source.git "https://github.com/yatima-inc/Ipld.lean.git" "7e8ec7082e324bf0decdec24c278491d07bfd3e6"
  }]
}
