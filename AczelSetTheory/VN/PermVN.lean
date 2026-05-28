/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/PermVN.lean
--
-- Permutaciones sobre segmentos de Von Neumann: módulo de paridad estructural.
--
-- Estado: ✅ Stub-documento.
--   El contenido sustantivo de Peano `Combinatorics/Perm.lean`
--   (`FunPerm.comp`, `Sym A := FunPerm A`) ya está formalizado en
--   `AczelSetTheory/VN/SymGroupVN.lean` sobre el segmento `vnSeg n`.
--   Las secciones §3 (ciclos), §4 (signatura) y §5 (aplicaciones) son
--   TODO en Peano (placeholders sin contenido), por lo que la paridad
--   estructural está alcanzada al nivel actual de Peano.
--
-- Tabla de correspondencia:
--   Peano                                  Aczel
--   -----                                  -----
--   Perm.FunPerm A                         FunPerm A (re-exportado vía Peano)
--   Perm.FunPerm.comp                      AczelSetTheory.VN.SymVN.comp
--   Perm.Sym A                             AczelSetTheory.VN.SymVN n
--   Perm.card_Sym (placeholder rfl)        AczelSetTheory.VN.vnSeg_card
--   §3 ciclos (TODO en Peano)              — (sin contenido en ambos lados)
--   §4 sign (TODO en Peano)                — (sin contenido en ambos lados)

import AczelSetTheory.VN.SymGroupVN
import Peano.PeanoNat.Combinatorics.Perm

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace Perm

      /-!
      # § Paridad Perm
      Ver tabla de correspondencia en la cabecera del archivo.
      El contenido sustantivo vive en `AczelSetTheory.VN.SymGroupVN`.
      !-/

    end Perm
  end VN
end AczelSetTheory
