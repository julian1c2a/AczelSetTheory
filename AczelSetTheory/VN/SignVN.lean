/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/SignVN.lean
--
-- Signatura de permutaciones sobre el embedding de Von Neumann.
--
-- Estado: ⚠️ STUB HUÉRFANO — no se materializará por transporte.
--   Por ADR-000 (DECISIONS.md, 2026-05-30): Peano queda congelado para teoría
--   "hacia arriba" y la teoría nueva NO se transporta vía VN. La signatura de
--   permutaciones (sgn σ ∈ {+1,−1}, homomorfismo Sₙ → ℤ/2) se construirá, cuando
--   se aborde, de forma NATIVA en `AczelSetTheory/Combinatorics/` (sobre SymGroup
--   nativo), no aquí.
--   Este archivo se conserva solo como marcador histórico de la fase de paridad
--   Peano↔Aczel (bootstrapping). Candidato a retirar.
--
-- Contenido:
--   (vacío — placeholder histórico, ver Combinatorics/ para la teoría nativa)

import AczelSetTheory.VN.SymGroupVN
import Peano.PeanoNat.Combinatorics.Sign

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace Sign

      /-!
      # § 1. Definición
      !-/
      -- ...

      /-!
      # § 2. Propiedades
      !-/
      -- ...

      /-!
      # § 3. Aplicaciones
      !-/
      -- ...

    end Sign
  end VN
end AczelSetTheory
