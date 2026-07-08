import Lake
open Lake DSL

package "aczelsettheory"

require peanolib from "E:/Dropbox/GitHub/lean4/Peano"

lean_lib "AczelSetTheory"

@[default_target]
lean_exe "aczelsettheory" where
  root := `Main
