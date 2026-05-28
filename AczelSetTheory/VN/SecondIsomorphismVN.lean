/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/SecondIsomorphismVN.lean
--
-- Segundo Teorema de Isomorfía: paridad con Peano
-- `Combinatorics/GroupTheory/SecondIsomorphism.lean`.
--
-- Estado: ✅ Stub-doc.
--   El contenido sustantivo vive en `AczelSetTheory/Algebra/SecondIsomorphism.lean`
--   (`HFSubgroup.secondIsoMap`, `secondIsoMap_bijective`). La versión abstracta
--   sobre `HFGroup` es más general que la concreta `FinGroup ℕ₀` de Peano.
--
-- Tabla de correspondencia:
--   Peano                                  Aczel
--   -----                                  -----
--   subgroupHN                             HFSubgroup.subgroupHN
--   H_le_subgroupHN / N_le_subgroupHN      H_le_subgroupHN / N_le_subgroupHN
--   N_in_subgroupHN                        HFSubgroup.N_in_subgroupHN
--   N_normal_in_subgroupHN                 N_normal_in_subgroupHN
--   interHN_as_subgroup_H                  HFSubgroup.interHN_as_subgroup_H
--   interHN_as_subgroup_H_isNormal         interHN_as_subgroup_H_isNormal
--   secondIsoMap_welldefined               secondIsoMap_welldefined
--   secondIsoMap (H/(H∩N) → HN/N)          HFSubgroup.secondIsoMap
--   secondIsoMap_injective                 secondIsoMap_injective
--   secondIsoMap_surjective                secondIsoMap_surjective
--   secondIsoMap_bijective (2º TI)         secondIsoMap_bijective

import AczelSetTheory.Algebra.SecondIsomorphism
import Peano.PeanoNat.Combinatorics.GroupTheory.SecondIsomorphism

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace SecondIsomorphism

      /-!
      # § Paridad SecondIsomorphism
      Ver tabla de correspondencia en la cabecera del archivo.
      El contenido sustantivo vive en `AczelSetTheory.Algebra.SecondIsomorphism`.
      !-/

    end SecondIsomorphism
  end VN
end AczelSetTheory
