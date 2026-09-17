import Lake
open Lake DSL

package "aczelsettheory"

-- ⚠️ Era `from "E:/Dropbox/GitHub/lean4/Peano"`: una ruta ABSOLUTA de Windows, que sólo
-- existe en una máquina. Ningún runner de CI ni ningún otro clon podía resolverla.
-- `../Peano` es la MISMA carpeta aquí y funciona en todas partes; la CI clona Peano
-- como hermana (ver .github/workflows/build.yml).
require peanolib from "../Peano"

lean_lib "AczelSetTheory"

@[default_target]
lean_exe "aczelsettheory" where
  root := `Main
