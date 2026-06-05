/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/CorrespondenceTheoremVN.lean
--
-- Teorema de Correspondencia (Cuarto Teorema de Isomorfía): paridad con Peano
-- `Combinatorics/GroupTheory/CorrespondenceTheorem.lean`.
--
-- Estado: ✅ Documento de paridad.
--   El contenido sustantivo vive en `AczelSetTheory/Algebra/CorrespondenceTheorem.lean`
--   (`HFSubgroup.preimageSubgroup`, `mem_preimageSubgroup_iff`,
--   `N_le_preimageSubgroup`, `imageSubgroup_preimage`, `preimageSubgroup_image`).
--   La versión abstracta sobre `HFGroup` es más general que la concreta
--   `FinGroup ℕ₀` de Peano.
--
-- Tabla de correspondencia:
--   Peano                                  Aczel
--   -----                                  -----
--   imageSubgroup G N hn K hNK             HFSubgroup.KmodN_subgroup sub_N sub_K hn_N hNK
--   preimageSubgroup G N hn Q              HFSubgroup.preimageSubgroup sub_N hn_N Q
--   mem_preimageSubgroup_iff               HFSubgroup.mem_preimageSubgroup_iff
--   N_le_preimageSubgroup                  HFSubgroup.N_le_preimageSubgroup
--   imageSubgroup_preimage (φ∘ψ = id)      HFSubgroup.imageSubgroup_preimage  (igualdad como HFSet)
--   preimageSubgroup_image (ψ∘φ = id)      HFSubgroup.preimageSubgroup_image  (igualdad como HFSet)
--   SubgroupAbove G N hn                   (subtipo implícito; HFSet)
--   correspondencePhi / Psi                (no se materializan: la biyección
--                                           ya se sigue de las dos igualdades de portador)
--   correspondenceInjective/Surjective     (corolarios inmediatos)
--   preimage_subgroup_card                 no materializado aquí (requiere Lagrange sobre HFSubgroup)
--
-- Nota: Peano usa `leftCoset` y Aczel usa `rightCoset`; la teoría es simétrica.

import AczelSetTheory.Algebra.CorrespondenceTheorem
import Peano.PeanoNat.Combinatorics.GroupTheory.CorrespondenceTheorem

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace CorrespondenceTheorem

      /-!
      # § Paridad CorrespondenceTheorem
      Ver tabla de correspondencia en la cabecera del archivo.
      El contenido sustantivo vive en `AczelSetTheory.Algebra.CorrespondenceTheorem`.
      !-/

    end CorrespondenceTheorem
  end VN
end AczelSetTheory
