/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/QuotientGroupVN.lean
--
-- Grupo cociente: paridad con Peano `Combinatorics/GroupTheory/QuotientGroup.lean`.
--
-- Estado: ✅ Documento de paridad.
--   El contenido sustantivo vive en `AczelSetTheory/Algebra/QuotientGroup.lean`
--   (`quotientGroup`, `quotientHom`, `ker_quotientHom_eq`). La versión abstracta
--   sobre `HFGroup` es más general que la versión concreta `FinGroup ℕ₀` de Peano.
--
-- Tabla de correspondencia:
--   Peano                                  Aczel
--   -----                                  -----
--   quotientCarrier G H                    sub.cosets   (right cosets via CosetCount)
--   cosetRepOf G H C                       HFSubgroup.cosetRep sub C
--   quotientOp_welldefined G H hn          HFSubgroup.quotientOp_welldefined
--   quotientOp G H hn                      HFSubgroup.quotientOp
--   quotientGroup G H hn                   quotientGroup grp sub hn
--   quotientHomomorphism G H hn            quotientHom grp sub hn
--   ker_quotientHom = H                    ker_quotientHom_eq
--
-- Notas técnicas:
--   • El portador es `sub.cosets` (de `Algebra/CosetCount.lean`), evitando
--     reconstruir el conjunto de cosetes.
--   • `cosetRep` usa `Classical.choose`, por lo que la operación cociente
--     es `noncomputable`.
--   • La buena definición requiere normalidad (sub.isNormal).

import AczelSetTheory.Algebra.QuotientGroup
import Peano.PeanoNat.Combinatorics.GroupTheory.QuotientGroup

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace QuotientGroup

      /-!
      # § Paridad QuotientGroup
      Ver tabla de correspondencia en la cabecera del archivo.
      El contenido sustantivo vive en `AczelSetTheory.Algebra.QuotientGroup`.
      !-/

    end QuotientGroup
  end VN
end AczelSetTheory
