/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/FirstIsomorphismVN.lean
--
-- Primer Teorema de Isomorfía: paridad con Peano
-- `Combinatorics/GroupTheory/FirstIsomorphism.lean`.
--
-- Estado: ✅ Documento de paridad.
--   El contenido sustantivo vive en `AczelSetTheory/Algebra/FirstIsomorphism.lean`
--   (`HFGroupHom.firstIsoMap`, `firstIsoMap_bijective`). La versión abstracta sobre
--   `HFGroup` es más general que la versión concreta `FinGroup ℕ₀` de Peano.
--
-- Tabla de correspondencia:
--   Peano                                  Aczel
--   -----                                  -----
--   Injective / Surjective / Bijective     HFGroupHom.Injective / Surjective / Bijective
--   quotientHom_surjective                 quotientHom_surjective
--   imageInclusion                         HFGroupHom.imageInclusion
--   imageInclusion_injective               imageInclusion_injective
--   firstIsoMap_welldefined                firstIsoMap_welldefined
--   firstIsoMap (G/ker φ → im φ)           HFGroupHom.firstIsoMap
--   firstIsoMap_injective                  firstIsoMap_injective
--   firstIsoMap_surjective                 firstIsoMap_surjective
--   firstIsoMap_bijective (1er TI)         firstIsoMap_bijective

import AczelSetTheory.Algebra.FirstIsomorphism
import Peano.PeanoNat.Combinatorics.GroupTheory.FirstIsomorphism

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace FirstIsomorphism

      /-!
      # § Paridad FirstIsomorphism
      Ver tabla de correspondencia en la cabecera del archivo.
      El contenido sustantivo vive en `AczelSetTheory.Algebra.FirstIsomorphism`.
      !-/

    end FirstIsomorphism
  end VN
end AczelSetTheory
