/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/CountingVN.lean
--
-- Principios de conteo sobre el embedding de Von Neumann.
--
-- Estado: ⚠️ STUB HUÉRFANO — no se materializará por transporte.
--   Por ADR-000 (DECISIONS.md, 2026-05-30): Peano queda congelado para teoría
--   "hacia arriba" y la teoría nueva NO se transporta vía VN. El conteo nativo
--   vive en `AczelSetTheory/Combinatorics/Counting.lean` (pigeonhole ya demostrado:
--   `HFSet.pigeonhole`, `HFSet.exists_collision_of_card_lt`).
--   Este archivo se conserva solo como marcador histórico de la fase de paridad
--   Peano↔Aczel (bootstrapping). Candidato a retirar.
--
-- Contenido:
--   (vacío — placeholder histórico, ver Combinatorics/ para el conteo nativo)

import AczelSetTheory.VN.Basic
import AczelSetTheory.VN.FSet
import Peano.PeanoNat.Combinatorics.Counting

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace Counting

      /-!
      # § 1. Principios de conteo
      !-/
      -- ...

      /-!
      # § 2. Permutaciones y combinaciones
      !-/
      -- ...

      /-!
      # § 3. Aplicaciones
      !-/
      -- ...

    end Counting
  end VN
end AczelSetTheory
