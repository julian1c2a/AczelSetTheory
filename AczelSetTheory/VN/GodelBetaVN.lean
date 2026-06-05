/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/GodelBetaVN.lean
-- Transporte de la función β de Gödel de Peano a HFSet vía vN.
-- β(c, b, i) = c mod (1 + (i+1)·b); base de la codificación de listas en ℕ₀.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Foundation.GodelBeta

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definición
-- ─────────────────────────────────────────────────────────────────

/-- Función β de Gödel transportada: vN (beta c b i). -/
def betaVN (c b i : ℕ₀) : HFSet := vN (beta c b i)

-- ─────────────────────────────────────────────────────────────────
-- Propiedad principal: β(a, b, i) = a cuando a < 1 + (i+1)·b
-- ─────────────────────────────────────────────────────────────────

-- gmod b i := add 𝟙 (mul (σ i) b) — abbrev privado en GodelBeta, usamos su definición.
theorem vN_beta_of_lt (a b i : ℕ₀)
    (h : Peano.StrictOrder.lt₀ a (add 𝟙 (mul (σ i) b))) :
    vN (beta a b i) = vN a :=
  congrArg vN (beta_of_lt a b i h)

end VN
