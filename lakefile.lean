import Lake
open Lake DSL

package "aczelsettheory"

lean_lib "AczelSetTheory" where
  -- Esto le dice a Lake que los fuentes de la librería están en la carpeta `AczelSetTheory/`
  srcDir := "AczelSetTheory"

@[default_target]
lean_exe "aczelsettheory" where
  root := `Main
