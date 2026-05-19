/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/TotientVN.lean
-- Transporte de la función φ de Euler (totient) de Peano a HFSet vía vN.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.NumberTheory.Totient

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definición
-- ─────────────────────────────────────────────────────────────────

/-- Función de Euler φ(n) transportada: vN (totient n). -/
def totientVN (n : ℕ₀) : HFSet := vN (totient n)

-- ─────────────────────────────────────────────────────────────────
-- Casos base
-- ─────────────────────────────────────────────────────────────────

theorem vN_totient_zero : vN (totient 𝟘) = vN 𝟘 :=
  congrArg vN totient_zero

theorem vN_totient_one : vN (totient 𝟙) = vN 𝟙 :=
  congrArg vN totient_one

theorem vN_totient_two : vN (totient 𝟚) = vN 𝟙 :=
  congrArg vN totient_two

-- ─────────────────────────────────────────────────────────────────
-- Propiedades básicas
-- ─────────────────────────────────────────────────────────────────

/-- φ(p) = p - 1 para p primo. -/
theorem vN_totient_prime {p : ℕ₀} (hp : Arith.Prime p) :
    vN (totient p) = vN (Peano.Sub.sub p 𝟙) :=
  congrArg vN (totient_prime hp)

end VN
