/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/NormalSubgroupVN.lean
--
-- Subgrupos normales: módulo de paridad estructural con Peano.
--
-- Estado: ✅ Stub-documento.
--   El contenido sustantivo (centralizer, center, normalizer, criterios
--   de normalidad: N_G(H)=G y gH=Hg) ya está formalizado en
--   `AczelSetTheory/Algebra/NormalSubgroup.lean` sobre `HFGroup` abstracto.
--   Este módulo existe únicamente para registrar la correspondencia
--   estructural con `Peano.PeanoNat.Combinatorics.GroupTheory.NormalSubgroup`
--   (versión sobre `FinGroup ℕ₀`).
--
-- Tabla de correspondencia:
--   Peano                                      Aczel
--   -----                                      -----
--   Subgroup G (FinGroup ℕ₀)                   HFSubgroup grp
--   Subgroup.IsNormal                          HFSubgroup.isNormal
--   centralizer G H                            HFAlgebra.centralizer sub
--   center G                                   HFAlgebra.center grp
--   normalizer G H                             HFAlgebra.normalizer sub
--   mem_centralizer_iff                        HFAlgebra.mem_centralizer_iff
--   mem_center_iff                             HFAlgebra.mem_center_iff
--   mem_normalizer_iff                         HFAlgebra.mem_normalizer_iff
--   H_subset_normalizer                        HFAlgebra.H_subset_normalizer
--   isNormal_iff_normalizer_eq_G               HFAlgebra.isNormal_iff_normalizer_eq_G
--   isNormal_iff_leftCoset_eq_rightCoset       HFAlgebra.isNormal_iff_cosets_eq
--   center_isNormal                            (derivable; ver Algebra/NormalSubgroup)
--   ker_isNormal (de Group.lean en Peano)      HFAlgebra.HFGroupHom.ker_isNormal
--
-- Un bridge explícito `FinGroup ℕ₀ → HFGroup` (que transportaría literalmente
-- las pruebas de Peano) no se requiere para paridad: la versión abstracta
-- de Aczel ya cubre los mismos teoremas con el mismo nivel de generalidad
-- (de hecho, mayor: sobre HFGroup arbitrario en lugar de FinGroup finito).

import AczelSetTheory.Algebra.NormalSubgroup
import Peano.PeanoNat.Combinatorics.GroupTheory.NormalSubgroup

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace NormalSubgroup

      /-!
      # § Paridad NormalSubgroup
      Ver tabla de correspondencia en la cabecera del archivo.
      Sin contenido ejecutable: el contenido sustantivo vive en
      `AczelSetTheory.Algebra.NormalSubgroup`.
      !-/

    end NormalSubgroup
  end VN
end AczelSetTheory
