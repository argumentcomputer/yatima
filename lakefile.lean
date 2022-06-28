import Lake

open Lake DSL

package Yatima {
  supportInterpreter := true
  binName := "yatima"
  dependencies := #[{
    name := `Ipld
    src := Source.git "https://github.com/yatima-inc/Ipld.lean.git" "9d2f32738cffb83e96a07845824cb489a1dcf081"
  }, {
    name := `YatimaStdLib 
    src := Source.git "https://github.com/yatima-inc/YatimaStdLib.lean.git" "10110f7311a83c76a0f83f709b8ceea3abcb76e9" 
  }]
}
