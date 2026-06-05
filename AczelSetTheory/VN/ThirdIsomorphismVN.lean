/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/ThirdIsomorphismVN.lean
--
-- Tercer Teorema de Isomorfía: paridad con Peano
-- `Combinatorics/GroupTheory/ThirdIsomorphism.lean`.
--
-- Estado: ✅ Documento de paridad.
--   El contenido sustantivo vive en `AczelSetTheory/Algebra/ThirdIsomorphism.lean`
--   (`HFSubgroup.thirdIsoMap`, `thirdIsoMap_surjective`, `thirdIsoMap_ker_eq`).
--   La versión abstracta sobre `HFGroup` es más general que la concreta
--   `FinGroup ℕ₀` de Peano.
--
-- Tabla de correspondencia:
--   Peano                                  Aczel
--   -----                                  -----
--   cosetRel_N_imp_K                       (consecuencia de hNK + cosetEq)
--   KmodN_subgroup (= imageSubgroup)       HFSubgroup.KmodN_subgroup
--   KmodN_normal                           HFSubgroup.KmodN_normal
--   thirdIsoMap_welldefined                thirdIsoMap_welldefined
--   thirdIsoMap (G/N → G/K)                HFSubgroup.thirdIsoMap
--   thirdIsoMap_op / id / inv              (incluidos en f_hom de thirdIsoMap)
--   thirdIsoGroupHom                       HFSubgroup.thirdIsoMap (es HFGroupHom)
--   thirdIsoMap_surjective                 thirdIsoMap_surjective
--   thirdIsoMap_kernel                     thirdIsoMap_ker_eq

import AczelSetTheory.Algebra.ThirdIsomorphism
import Peano.PeanoNat.Combinatorics.GroupTheory.ThirdIsomorphism

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace ThirdIsomorphism

      /-!
      # § Paridad ThirdIsomorphism
      Ver tabla de correspondencia en la cabecera del archivo.
      El contenido sustantivo vive en `AczelSetTheory.Algebra.ThirdIsomorphism`.
      !-/

    end ThirdIsomorphism
  end VN
end AczelSetTheory
