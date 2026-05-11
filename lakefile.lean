import Lake
open Lake DSL

package "aczelsettheory"

require peanolib from git
  "https://github.com/julian1c2a/Peano" @ "master"

lean_lib "AczelSetTheory"

@[default_target]
lean_exe "aczelsettheory" where
  root := `Main
