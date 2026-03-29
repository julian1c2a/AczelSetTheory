import Lake
open Lake DSL

package "aczelsettheory"

lean_lib "AczelSetTheory"

@[default_target]
lean_exe "aczelsettheory" where
  root := `Main
