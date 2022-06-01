import Lake

open Lake DSL

package Yatima {
  supportInterpreter := true
  binName := "yatima"
  dependencies := #[{
    name := `Ipld
<<<<<<< HEAD
    src := Source.git "https://github.com/yatima-inc/Ipld.lean.git" "9d2f32738cffb83e96a07845824cb489a1dcf081"
=======
    src := Source.git "https://github.com/yatima-inc/Ipld.lean.git" "update-repo"
>>>>>>> 15c9345 (Revert "Revert "removing IPLD code and importing from repo instead (#38)"")
  }]
}
