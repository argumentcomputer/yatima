import Lake

open Lake DSL

package Yatima {
  supportInterpreter := true
  binName := "yatima"
  dependencies := #[{
    name := `Ipld
    src := Source.git "https://github.com/yatima-inc/Ipld.lean.git" "9d2f32738cffb83e96a07845824cb489a1dcf081"
  }]
}
