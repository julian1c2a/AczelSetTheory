import Lake
open Lake DSL

package "aczelsettheory"

require peanolib from "E:/dropbox/github/lean4/peano"

lean_lib "AczelSetTheory"

@[default_target]
lean_exe "aczelsettheory" where
  root := `Main
