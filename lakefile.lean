import Lake
open Lake DSL

package "aczelsettheory"

require peanolib from "E:/dropbox/github/lean4/Peano.worktrees/arith-expansion"

lean_lib "AczelSetTheory"

@[default_target]
lean_exe "aczelsettheory" where
  root := `Main
